
Are we have syntax adn semantics of typed rules described somewhere?

in  docs/proposals/042-explicit-type-parameters-on-operations.md we wrote about types erasure, but is it?
in

We have re[resentation of rules as streams in 052-rules-as-stream-valued-operations.md
 and from this folllows, that type-variables on rules should be the same as on operations
  but it is not described (gap in 052)

We have description of types rules syntax in  docs/design/constrained-term-substrate.md 
 but looks like not in any of formal propsal. 

Semantics of typed rules is not defined,  explicit question is in WI-742 anthill-todo workitem.

So, we need write a proposal and define semantic

Now - variants of interpratation of typed rules (what means x:T) ?

arguments substitution

1.A) have special type-rule (optional ty field in value, which was at first introduced and then deleted).
  We can statically make typed(v,type) expression and insert it in arguments where we call typed rule.
 (it was deleted becasue we does not start building typed value rules immediatly aftet substrate and it looks lie yet unused)

 p(x:Color, y:Color, z:Int64) :- x != y , c(y,z)

   call p(x,y)

1.B) - have typed term

 p(?x:Color, ?y:Color, ?z:Int64) :- ?x != ?y , c(?y,?z)
  can be translated to
    p(?x=typed(?x1,Color),?y=typed(?y1,Color),?z=typed(?z1,Int64)) :- 
           

1.C) have values untyped, but instead append typed guard, and have in type standard set of typeclasses, which
 can be used if typed

 p(?x:Color, ?y:Color, ?z:Int64) :- ?x != ?y , c(?y,?z)

  can be transformed to

 p(?x:Color, ?y:Color, ?z:Int64) :- is_type(?x,Color), is_type(?y,Color), is_type(?z,Int64),
                                       ?x != ?y , c(?y,?z)
  this can allow bound to rules standard rules for given types (such as values in enum, so we can not use palette in colours example)

  qustion - can we use discriminator tree to fast type dispath ? Maybe recognize is_type specially.

  Maybe we can unite B and C :  transform calls into typed(x,T) wih support from multiple typed calls in discriminator tree.

Semantic of type-var in rule head

2.A) - yet one logical value, which carry type

 
 p[T](x:T,y:T,z:Int64) :- ?x != ?y, c(?y,?z)


 for 1.C
   p(?x,?y,?z,?T) :- rule_type(?T), is_type(?x,?T), is_type(?y,?T), is_type(?z,Int64) ?x != ?y, c(?y,?z)
  


B) -  hight-order rule:

 p[T](x:T,y:T,z:Int64) :- ?x != ?y, c(?y,?z)
 
   Pt(?t)(p'(?x,?y,?z) :- rule_type(?t), is_type(?x,?t), ..... 

C) - hight-level substitution

  p(?T)(p'(?x,?y,?z)) <=> subst(p'(?x,?y,?z),T,?T)

Not fully cleam, let think


Bouns question: can we in typed rules use x:Int instead ?x:Int 


