

Let create an example, which emulate the solution to the "Guaridans of the Agents" challenge,
   https://cacm.acm.org/practice/guardians-of-the-agents/

The idea - we should design API which allows us to generate safe agent which will classify email and be resilient to prompt injection attacks in email.

Other implementations described:
    - Scala:  article: https://arxiv.org/html/2603.00991v2
           inplementation:  https://github.com/lampepfl/tacit

    - Python + Dafny/Z3:
           implementation: https://github.com/metareflection/guardians

    - ETAS: https://arxiv.org/abs/2607.17780
        

Use effects tracking for analyzing of generated API and design embedding of LLM-agent generation into logical part
 in such way, that task formulated declaratively.
