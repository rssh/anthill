# Conversational Specification

## Problem

Today, developers starting a new project typically begin with UI wireframes. Domain models emerge as a side effect of layout decisions — database schemas are shaped by what forms need, not by what the domain actually is.

```
"I want to sell tickets"
  → draw wireframes
  → "OK there's a page with events, a buy button, a form..."
  → start coding: components, API routes, DB tables
  → domain model emerges accidentally from UI
```

## Insight

Anthill's logical variables (`?`) are the formal equivalent of a rough sketch. `sort Price = ?` means "I know Price exists but I don't know what it is yet." The language already supports incremental, vague specification — the gap is workflow.

## Approach: LLM + KB as Shared State

An LLM agent mediates between natural-language conversation and the anthill knowledge base. The developer talks; the LLM reads/writes the KB; the KB validates consistency.

```
     chat (natural language)
       ↕
      LLM  ←→  KB (anthill spec with ? holes)
       ↕
     validation / remaining holes
```

### Example Session

```
Developer: "I want to sell tickets"

LLM → KB:
  sort TicketSales = ? {< a ticket sales system >} ?

LLM → Developer: "What do you sell tickets for?"
```

```
Developer: "concerts and sports events"

LLM → KB:
  sort Event = ? {< a concert or sports event >} ?
  sort Ticket = ? {< purchasable for an event >} ?

LLM → Developer: "Can tickets be refunded?"
```

```
Developer: "yes, but only before the event date"

LLM → KB:
  operation refund(t: Ticket) -> Ticket
    requires before(now(), date(event(?t)))

  -- constraint implies Event needs a date:
  entity Event(..., date: Date)

LLM → Developer: "What information does a Ticket have?"
```

### What the LLM Does at Each Step

Every LLM response either:
- **Adds** new constructs (sort, entity, operation, constraint)
- **Refines** a `?` into something concrete
- **Asks** about a remaining `?`

The KB provides:
- **Validation** — catches inconsistencies ("you said capacity is Int but used it as String")
- **Hole enumeration** — lists remaining `?` to guide the conversation
- **Implication tracking** — `requires before(now(), date(event(?t)))` implies Event needs a `date` field

### The Spec Grows Organically

```
-- after 2 minutes of chat:

sort TicketSales = ? {< a ticket sales system >} ?
sort Event = ? {< a concert or sports event >} ?
sort Ticket = ? {< purchasable for an event >} ?

-- after 10 minutes:

sort TicketSales {
  sort Event = ? {< a concert or sports event >} ?
  sort Ticket = ? {< purchasable for an event >} ?
  sort Customer = ? {< someone who buys tickets >} ?
  sort Order = ? {< result of a purchase >} ?

  entity Event(name: String, venue: ?, capacity: Int, date: Date)
  entity Ticket(event: Event, seat: ?, price: Money)

  operation purchase(c: Customer, e: Event, qty: Int) -> Order
    requires gt(qty, 0)
    requires lte(add(sold(?e), qty), capacity(?e))
    effects (Modify{orders}, Emit{Notification})

  operation refund(t: Ticket) -> Ticket
    requires before(now(), date(event(?t)))

  constraint capacity: lte(sold(?e), capacity(?e))
}
```

Every intermediate state is valid anthill. The developer can stop at any point and have a meaningful (if incomplete) specification.

## What This Requires

**Language**: Nothing new. `sort T = ?`, description blocks, and existing constructs are sufficient.

**Tooling**:
- LLM with tool-use access to KB operations (`assert_fact`, `define_sort`, `add_operation`, `add_constraint`)
- Hole enumeration: query for all unresolved `?` in the current spec
- Validation feedback: report constraint violations and type mismatches to the LLM
- Spec rendering: show current anthill spec to the developer at any point

## Key Property

The conversation is just the interface. The KB is the shared state. This means:
- Multiple developers can contribute to the same spec via separate conversations
- The LLM's suggestions are always grounded in the current KB state
- The spec is never "lost in chat" — it's always in the KB
- The developer can switch from chat to directly editing anthill at any point
