Notes
=====

A tutorial implementation of a dependently typed lambda calculus
=================
Andres Loh


follow the paper? there are good pointers on implementation

dont want beta reduction in data types tho e.g. Vec (1+1) String should not be a valid type, because (+) is a **def**intion/function symbol and not a datatype symbol



Abstract Refinement Types
=========================
Niki Vazou1, Patrick M. Rondon2, and Ranjit Jhala1
http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf

we are trying to do something similar as they do in this paper, namely attach refinement types to datatype definitions



Elaboration in Dependent Type Theory
====================================
Leonardo de Moura1, Jeremy Avigad*2, Soonho Kong3, and Cody Roux4


What they do in lean... again we probably dont want full dependent type theory




Proofs and Programs about Open Terms
====================================
Francisco Ferreira Ruiz

this is where the idea for contexts came from. i didnt quite get what they do here tho. might have to look again a bit more carefully?


Idris, a General Purpose Dependently Typed Programming Language: Design and Implementation
===================
EDWIN BRADY

ideas about implicit type parameters being automatically expanded by program transformation