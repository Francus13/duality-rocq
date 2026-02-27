From Stdlib Require Import
  Logic.FunctionalExtensionality
  Program.Basics
  List
  Lia.
  
  (* Syntax ------------------------------------------------------ *)

(*  This is a bare-bones language for exploring about how
    pure and direct data (values) and codata (covalues)
    interact via mutual deconstruction.

    Values are direct data: unit, pairs, injections.
    Covalues are direct codata: counit, copairs, projections.

    Values are well-understood, but covalues are less intuitive:
    Covalues are constructs for the elimination forms of values.
    - Counit eliminates unit (and vice versa).
    - Copairs are essentially pattern matchings that continue
      with covalues. Dual to how pairs can be destructed with 
      pattern matchings (copairs) or projections, copairs can be 
      destructed with pairs or injections.
    - Projections are the dual (but not eliminator) of injections.

    White and black holes are constructs that trivially deconstruct
    any covalue and value, respectively. I think these correspond
    to constructions for 0 and Top? They aren't necessary to this
    language, and can be excluded statically if desired.
    - Of note, an injection inl v is subsumed by the pair (v, wh)
      in the sense that any eliminator of inl v also equivalently
      elminates (v, wh) (and same with the dual).
 *)

Inductive value :=
| unit
| white_hole
| pair (v1 v2 : value)
| inl (v : value)
| inr (v : value)
.

Inductive covalue :=
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



(* Semantics --------------------------------------------------- *)

(*  
 *)

Inductive lin_destr : covalue -> value -> Prop :=
| cut_units :     (* [] | () *)
      lin_destr ( %[] ) ( $() )

| cut_wh :        (* c | wh *)
    forall c,
      lin_destr c ( $wh )
| cut_bh :        (* bh | v *)
    forall v,
      lin_destr ( %bh ) v

| cut_pairs :     (* [c1, c2] | (v1, v2) *)
    forall c1 c2 v1 v2,
      lin_destr c1 v1 ->
      lin_destr c2 v2 ->
      lin_destr ( %[c1, c2] ) ( $(v1, v2) )

| cut_inl :       (* [c1, c2] | inl v *)
    forall c1 c2 v,
      lin_destr c1 v ->
      lin_destr ( %[c1, c2] ) ( $inl v )
| cut_inr :       (* [c1, c2] | inr v *)
    forall c1 c2 v,
      lin_destr c2 v ->
      lin_destr ( %[c1, c2] ) ( $inr v )

| cut_fst :       (* fst c | (v1, v2) *)
    forall c v1 v2,
      lin_destr c v1 ->
      lin_destr ( %fst c ) ( $(v1, v2) )
| cut_snd :       (* snd c | (v1, v2) *)
    forall c v1 v2,
      lin_destr c v2 ->
      lin_destr ( %snd c ) ( $(v1, v2) )
.



(*  
 *)

Inductive result :=
| r_val (v : value)
| r_cov (c : covalue)
.

Inductive big_step : covalue -> value -> list result -> Prop :=
| bs_units :     (* [] | ()  =>  nil *)
      big_step ( %[] ) ( $() ) nil
| bs_unit :     (* c | ()  =>  c *)
    forall c,
      ~(c = ( %[] )) ->
      big_step c ( $() ) ((r_cov c) :: nil)
| bs_counit :     (* [] | v  =>  v *)
    forall v,
      ~(v = ( $() )) ->
      big_step ( %[] ) v ((r_val v) :: nil)

| bs_wh :        (* c | wh  =>  nil *)
    forall c,
      big_step c ( $wh ) nil
| bs_bh :        (* bh | v  =>  nil *)
    forall v,
      big_step ( %bh ) v nil

| bs_pairs :     (* [c1, c2] | (v1, v2)  =>  (c1 | v1) ++ (c2 | v2) *)
    forall c1 c2 v1 v2 r1 r2,
      big_step c1 v1 r1 ->
      big_step c2 v2 r2 ->
      big_step ( %[c1, c2] ) ( $(v1, v2) ) (r1 ++ r2)

| bs_inl :       (* [c1, c2] | inl v  =>  (c1 | v) *)
    forall c1 c2 v r,
      big_step c1 v r ->
      big_step ( %[c1, c2] ) ( $inl v ) r
| bs_inr :       (* [c1, c2] | inr v  =>  (c2 | v) *)
    forall c1 c2 v r,
      big_step c2 v r ->
      big_step ( %[c1, c2] ) ( $inr v ) r

| bs_fst :       (* fst c | (v1, v2)  =>  (c | v1) *)
    forall c v1 v2 r,
      big_step c v1 r ->
      big_step ( %fst c ) ( $(v1, v2) ) r
| bs_snd :       (* snd c | (v1, v2)  =>  (c | v2) *)
    forall c v1 v2 r,
      big_step c v2 r ->
      big_step ( %snd c ) ( $(v1, v2) ) r
.



(*  
 *)

Inductive partial_value :=
| p_val (v : value)
| p_null
| p_pair (p1 p2 : partial_value)
.

Inductive val_cut : value -> value -> partial_value -> Prop :=
| vc_units :     (* () | ()  =>  null *)
      val_cut ( $() ) ( $() ) p_null
| vc_r_unit :     (* v | ()  =>  v *)
    forall v,
      ~(v = ( $() )) ->
      val_cut v ( $() ) (p_val v)
| vc_l_unit :     (* () | v  =>  v *)
    forall v,
      ~(v = ( $() )) ->
      val_cut ( $() ) v (p_val v)

| vc_r_wh :        (* v | wh  =>  null *)
    forall v,
      val_cut v ( $wh ) p_null
| vc_l_wh :        (* wh | v  =>  null *)
    forall v,
      val_cut ( $wh ) v p_null

| vc_pairs :     (* (v1, v2) | (v1', v2')  =>  ((v1 | v1'), (v2 | v2')) *)
    forall v1 v2 v1' v2' p1 p2,
      val_cut v1 v1 p1 ->
      val_cut v2 v2 p2 ->
      val_cut ( $(v1, v2) ) ( $(v1', v2') ) (p_pair p1 p2)

| vc_r_inl :       (* (v1, v2) | inl v  =>  (v1 | v) *)
    forall v1 v2 v p,
      val_cut v1 v p ->
      val_cut ( $(v1, v2) ) ( $inl v ) p
| vc_r_inr :       (* (v1, v2) | inr v  =>  (v2 | v) *)
    forall v1 v2 v p,
      val_cut v2 v p ->
      val_cut ( $(v1, v2) ) ( $inr v ) p

| vc_l_inl :       (* inl v | (v1, v2)  =>  (v | v1) *)
    forall v v1 v2 p,
      val_cut v v1 p ->
      val_cut ( $inl v ) ( $(v1, v2) ) p
| vc_l_inr :       (* inr v | (v1, v2)  =>  (v | v2) *)
    forall v v1 v2 p,
      val_cut v v2 p ->
      val_cut ( $inr v ) ( $(v1, v2) ) p
.


Fixpoint flatten_partial_value (p : partial_value) : option value :=
match p with
| p_val v => Some v
| p_null => None
| p_pair p1 p2 => match flatten_partial_value p1 with
                  | None => flatten_partial_value p2
                  | Some v1 => match flatten_partial_value p2 with
                               | None => Some v1
                               | Some v2 => Some ( $(v1, v2) )
                               end
                  end
end.



(*  
 *)

Inductive val_match_inj : value -> value -> value -> Prop :=
| vmi_r_unit :     (* v | ()  =>  v *)
    forall v,
      val_match_inj v ( $() ) v
| vmi_l_unit :     (* () | v  =>  v *)
    forall v,
      val_match_inj ( $() ) v v

| vmi_pairs :     (* (v1, v2) | (v1', v2')  =>  ((v1 | v1'), (v2 | v2')) *)
    forall v1 v2 v1' v2' rv1 rv2,
      val_match_inj v1 v1 rv1 ->
      val_match_inj v2 v2 rv2 ->
      val_match_inj ( $(v1, v2) ) ( $(v1', v2') ) ( $(rv1, rv2) )

| vmi_r_inl :       (* (v1, v2) | inl v  =>  (v1 | v) *)
    forall v1 v2 v rv,
      val_match_inj v1 v rv ->
      val_match_inj ( $(v1, v2) ) ( $inl v ) rv
| vmi_r_inr :       (* (v1, v2) | inr v  =>  (v2 | v) *)
    forall v1 v2 v rv,
      val_match_inj v2 v rv ->
      val_match_inj ( $(v1, v2) ) ( $inr v ) rv

| vmi_l_inl :       (* inl v | (v1, v2)  =>  (v | v1) *)
    forall v v1 v2 rv,
      val_match_inj v v1 rv ->
      val_match_inj ( $inl v ) ( $(v1, v2) ) rv
| vmi_l_inr :       (* inr v | (v1, v2)  =>  (v | v2) *)
    forall v v1 v2 rv,
      val_match_inj v v2 rv ->
      val_match_inj ( $inr v ) ( $(v1, v2) ) rv
.



(*  
 *)

Inductive val_match_wh : value -> value -> value -> Prop :=
| vmw_r_unit :     (* v | ()  =>  v *)
    forall v,
      val_match_wh v ( $() ) v
| vmw_l_unit :     (* () | v  =>  v *)
    forall v,
      val_match_wh ( $() ) v v

| vmw_pairs :     (* (v1, v2) | (v1', v2')  =>  ((v1 | v1'), (v2 | v2')) *)
    forall v1 v2 v1' v2' rv1 rv2,
      val_match_wh v1 v1 rv1 ->
      val_match_wh v2 v2 rv2 ->
      val_match_wh ( $(v1, v2) ) ( $(v1', v2') ) ( $(rv1, rv2) )

| vmw_r_lwh :       (* (v1, v2) | (v, wh)  =>  (v1 | v) *)
    forall v1 v2 v rv,
      val_match_wh v1 v rv ->
      val_match_wh ( $(v1, v2) ) ( $(v, $wh) ) rv
| vmw_r_rwh :       (* (v1, v2) | (wh, v)  =>  (v2 | v) *)
    forall v1 v2 v rv,
      val_match_wh v2 v rv ->
      val_match_wh ( $(v1, v2) ) ( $($wh, v) ) rv

| vmw_l_lwh :       (* (v, wh) | (v1, v2)  =>  (v | v1) *)
    forall v v1 v2 rv,
      val_match_wh v v1 rv ->
      val_match_wh ( $(v, $wh) ) ( $(v1, v2) ) rv
| vmw_l_rwh :       (* (wh, v) | (v1, v2)  =>  (v | v2) *)
    forall v v1 v2 rv,
      val_match_wh v v2 rv ->
      val_match_wh ( $($wh, v) ) ( $(v1, v2) ) rv
.

