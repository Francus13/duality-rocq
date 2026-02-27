From Stdlib Require Import
  Arith            
  Classes.RelationClasses
  Logic.FunctionalExtensionality
  Morphisms
  Program.Basics
  List
  Lia.



(* Raw de Bruijn Syntax ------------------------------------------------------ *)

(* Terms are a value and 

   There are two types of identifiers:

   Unrestricted (a.k.a. non-linear) Identifiers
    - these represent names of lambdas
    - by convention, we use [m : nat] to represent the number of such 
      identifies in scope within a term
    - we use [f] (for "function") and variants as the metavariable
      for writing down function identifiers

   Linear Identifiers
    - these represent "cuts" or "resource names" in the semantics
    - by convention, we use [n : nat] to represent the number of such
      identifiers in scope within a term
    - we use [r] (for "resource") and variants as the metavariable
      for writing down function identifiers 

   # Terms:

   A "term" [t] is a "bag" [bag m n P], consisting of a processes [P]. 
   It binds [m] (fresh) function identifiers and [n] (fresh) resource
   identifiers.

   # Processes:

   A process [P] is one of:
     - a definition [def r o] (written informally as "r <- o"),
       which defines the resource [r] as the operand [o]

     - a function application [f r].  Functions always take one
       argument, [r], and the function identifer [f] should be
       bound to a lambda somwehere in the context

     - two processes running "in parallel": [par P1 P2]

     - a null process: [nul]. Null does no computation,
       acting as the unit to par.

   # Operands:

   An operand [o] provides a definition of a resource identifier and
   can be one of:

     - emp          the empty tuple ()
     - [tup r1 r2]  a "tuple" (pair) of resources
     - [bng f]      the name of a function
     - [lam t]      an lambda, which is a term exactly one free resource

 *)

Inductive term :=
| duo (c : covalue) (v : value)

with value :=
| unit
| white_hole
| pair (v1 v2 : value)
| inl (v : value)
| inr (v : value)

with covalue :=
| counit
| black_hole
| copair (c1 c2 : covalue)
| fst (c : covalue)
| snd (c : covalue)
.

Notation "$()" := unit (at level 55).
Notation "$wh" := white_hole (at level 55).
Notation "$( v1 , v2 )" := (pair v1 v2) (at level 55).
Notation "$inl v" := (inl v) (at level 55).
Notation "$inr v" := (inr v) (at level 55).
Notation "%[]" := counit (at level 55).
Notation "%bh" := black_hole (at level 55).
Notation "%[ c1 , c2 ]" := (copair c1 c2) (at level 55).
Notation "%fst c" := (fst c) (at level 55).
Notation "%snd c" := (snd c) (at level 55).

