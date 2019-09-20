(*
 * Efficiently Executable Sets Library
 * Author: FireEye, Inc. - Formal Methods Team <formal-methods@fireeye.com>
 * 
 * Copyright (C) 2016 FireEye Technologie Deutschland GmbH
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library.
 * If not, see <http://www.gnu.org/licenses/>.
 *)

(** * Fold with abort for sets 

    This file provided an efficient fold operation for set interfaces.
    The standard fold iterates over all elements of the set. The
    efficient one - called [foldWithAbort] - is allowed to skip
    certain elements and thereby abort early.  
*)


Require Export MSetInterface.
Require Import mathcomp.ssreflect.ssreflect.
Require Import MSetWithDups.
Require Import Int.
Require Import MSetGenTree MSetAVL MSetRBT. 
Require Import MSetList MSetWeakList.


(** ** Fold With Abort Operations

    We want to provide an efficient folding operation. Efficieny is
    gained by aborting the folding early, if we know that continuing
    would not have an effect any more. Formalising this leads to the following
    specification of [foldWithAbort]. *)


Definition foldWithAbortType 
    elt (** element type of set *)
    t (** type of set *) 
    A (** return type *) :=
    (elt -> A -> A) ->    (** f *)
    (elt -> A -> bool) -> (** f_abort *)
    t ->                  (** input set *)
    A ->                  (** base value *)
    A.


Definition foldWithAbortSpecPred {elt t : Type} 
    (In : elt -> t -> Prop) 
    (fold : forall {A : Type}, (elt -> A -> A) -> t -> A -> A)
    (foldWithAbort : forall {A : Type}, foldWithAbortType elt t A) : Prop := 

    forall 
      (A : Type)
      (** result type *)    

      (i i' : A) 
      (** base values for foldWithAbort and fold *)

      (f : elt -> A -> A) (f' : elt -> A -> A) 
      (** fold functions for foldWithAbort and fold *)

      (f_abort : elt -> A -> bool) 
      (** abort function *)

      (s : t) (** sets to fold over *)

      (P : A -> A -> Prop) (** equivalence relation on results *),

    (** [P] is an equivalence relation *)
    Equivalence P ->
      
    (** [f] is for the elements of [s] compatible with the equivalence relation P *)
    (forall st st' e, In e s -> P st st' -> P (f e st) (f e st')) ->

    (** [f] and [f'] agree for the elements of [s] *)
    (forall e st, In e s -> (P (f e st) (f' e st))) ->       

    (** [f_abort] is OK, i.e. all other elements can be skipped without 
        leaving the equivalence relation. *)
    (forall e1 st, 
        In e1 s -> f_abort e1 st = true ->
        (forall st' e2, P st st' ->
                        In e2 s -> e2 <> e1 -> 
                        P st (f e2 st'))) ->

    (** The base values are in equivalence relation *)
    P i i' ->

    (** The results are in equivalence relation *)
    P (foldWithAbort f f_abort s i) (fold f' s i').


(** The specification of folding for ordered sets (as represented by
    interface [Sets]) demands that elements are visited in increasing
    order. For ordered sets we can therefore abort folding based on
    the weaker knowledge that greater elements have no effect on the
    result. The following definition captures this. *)

Definition foldWithAbortGtType 
    elt (** element type of set *)
    t (** type of set *) 
    A (** return type *) :=
    (elt -> A -> A) ->    (** f *)
    (elt -> A -> bool) -> (** f_gt *)
    t ->                  (** input set *)
    A ->                  (** base value *)
    A.


Definition foldWithAbortGtSpecPred {elt t : Type} 
    (lt : elt -> elt -> Prop) 
    (In : elt -> t -> Prop) 
    (fold : forall {A : Type}, (elt -> A -> A) -> t -> A -> A)
    (foldWithAbortGt : forall {A : Type}, foldWithAbortType elt t A) : Prop := 

    forall 
      (A : Type)
      (** result type *)    

      (i i' : A) 
      (** base values for foldWithAbort and fold *)

      (f : elt -> A -> A) (f' : elt -> A -> A) 
      (** fold functions for foldWithAbort and fold *)

      (f_gt : elt -> A -> bool) 
      (** abort function *)

      (s : t) (** sets to fold over *)

      (P : A -> A -> Prop) (** equivalence relation on results *),

    
    (** [P] is an equivalence relation *)
    Equivalence P ->

    (** [f] is for the elements of [s] compatible with the equivalence relation P *)
    (forall st st' e, In e s -> P st st' -> P (f e st) (f e st')) ->

    (** [f] and [f'] agree for the elements of [s] *)
    (forall e st, In e s -> (P (f e st) (f' e st))) ->       

    (** [f_abort] is OK, i.e. all other elements can be skipped without 
        leaving the equivalence relation. *)
    (forall e1 st, 
        In e1 s -> f_gt e1 st = true ->
        (forall st' e2, P st st' ->
                        In e2 s -> lt e1 e2 ->  
                        P st (f e2 st'))) ->

    (** The base values are in equivalence relation *)
    P i i' ->

    (** The results are in equivalence relation *)
    P (foldWithAbortGt f f_gt s i) (fold f' s i').



(** For ordered sets, we can safely skip elements at the end
    based on the knowledge that they are all greater than the current element.
    This leads to serious performance improvements for operations like
    filtering. It is tempting to try the symmetric operation and skip elements at
    the beginning based on the knowledge that they are too small to be interesting.
    So, we would like to start late as well as abort early. 

    This is indeed a very natural and efficient operation for set implementations 
    based on binary search trees (i.e. the AVL and RBT sets). We can completely symmetrically
    to skipping greater elements also skip smaller elements. This leads to the following
    specification. *)

Definition foldWithAbortGtLtType 
    elt (** element type of set *)
    t (** type of set *) 
    A (** return type *) :=
    (elt -> A -> bool) -> (** f_lt *)
    (elt -> A -> A) ->    (** f *)
    (elt -> A -> bool) -> (** f_gt *)
    t ->                  (** input set *)
    A ->                  (** base value *)
    A.


Definition foldWithAbortGtLtSpecPred {elt t : Type} 
    (lt : elt -> elt -> Prop) 
    (In : elt -> t -> Prop) 
    (fold : forall {A : Type}, (elt -> A -> A) -> t -> A -> A)
    (foldWithAbortGtLt : forall {A : Type}, foldWithAbortGtLtType elt t A) : Prop := 

    forall 
      (A : Type)
      (** result type *)    

      (i i' : A) 
      (** base values for foldWithAbort and fold *)

      (f : elt -> A -> A) (f' : elt -> A -> A) 
      (** fold functions for foldWithAbort and fold *)

      (f_lt f_gt : elt -> A -> bool) 
      (** abort functions *)

      (s : t) (** sets to fold over *)

      (P : A -> A -> Prop) (** equivalence relation on results *),

    
    (** [P] is an equivalence relation *)
    Equivalence P ->

    (** [f] is for the elements of [s] compatible with the equivalence relation P *)
    (forall st st' e, In e s -> P st st' -> P (f e st) (f e st')) ->

    (** [f] and [f'] agree for the elements of [s] *)
    (forall e st, In e s -> (P (f e st) (f' e st))) ->       

    (** [f_lt] is OK, i.e. smaller elements can be skipped without 
        leaving the equivalence relation. *)
    (forall e1 st, 
        In e1 s -> f_lt e1 st = true ->
        (forall st' e2, P st st' ->
                        In e2 s -> lt e2 e1 -> 
                        P st (f e2 st'))) ->

    (** [f_gt] is OK, i.e. greater elements can be skipped without 
        leaving the equivalence relation. *)
    (forall e1 st, 
        In e1 s -> f_gt e1 st = true ->
        (forall st' e2, P st st' ->
                        In e2 s -> lt e1 e2 -> 
                        P st (f e2 st'))) ->

    (** The base values are in equivalence relation *)
    P i i' ->

    (** The results are in equivalence relation *)
    P (foldWithAbortGtLt f_lt f f_gt s i) (fold f' s i').



(** We are interested in folding with abort mainly for runtime
    performance reasons of extracted code. The argument functions
    [f_lt], [f_gt] and [f] of [foldWithAbortGtLt] often share a large,
    comparably expensive part of their computation.

    In order to further improve runtime performance, therefore another
    version [foldWithAbortPrecompute f_precompute f_lt f f_gt] that
    uses an extra function [f_precompute] to allows to compute the
    commonly used parts of these functions only once. This leads to
    the following definitions. *)


Definition foldWithAbortPrecomputeType 
    elt (** element type of set *)
    t (** type of set *) 
    A (** return type *) 
    B (** type of precomputed results *) := 

    (elt -> B) ->               (** f_precompute *)
    (elt -> B -> A -> bool) ->  (** f_lt *)
    (elt -> B -> A -> A) ->     (** f *)
    (elt -> B -> A -> bool) ->  (** f_gt *)
    t ->                        (** input set *)
    A ->                        (** base value *)
    A.

(** The specification is similar to the one without precompute,
    but uses [f_precompute] so avoid doing computations multiple times *)
Definition foldWithAbortPrecomputeSpecPred {elt t : Type} 
    (lt : elt -> elt -> Prop) 
    (In : elt -> t -> Prop) 
    (fold : forall {A : Type}, (elt -> A -> A) -> t -> A -> A)
    (foldWithAbortPrecompute : forall {A B : Type}, foldWithAbortPrecomputeType elt t A B) : Prop := 

    forall 
      (A B : Type)
      (** result type *)    

      (i i' : A) 
      (** base values for foldWithAbortPrecompute and fold *)

      (f_precompute : elt -> B) 
      (** precompute function *)

      (f : elt -> B -> A -> A) (f' : elt -> A -> A) 
      (** fold functions for foldWithAbortPrecompute and fold *)

      (f_lt f_gt : elt -> B -> A -> bool) 
      (** abort functions *)

      (s : t) (** sets to fold over *)

      (P : A -> A -> Prop) (** equivalence relation on results *),

    
    (** [P] is an equivalence relation *)
    Equivalence P ->

    (** [f] is for the elements of [s] compatible with the equivalence relation P *)
    (forall st st' e, In e s -> P st st' -> P (f e (f_precompute e) st) (f e (f_precompute e) st')) ->

    (** [f] and [f'] agree for the elements of [s] *)
    (forall e st, In e s -> (P (f e (f_precompute e) st) (f' e st))) ->       

    (** [f_lt] is OK, i.e. smaller elements can be skipped without 
        leaving the equivalence relation. *)
    (forall e1 st, 
        In e1 s -> f_lt e1 (f_precompute e1) st = true ->
        (forall st' e2, P st st' ->
                        In e2 s -> lt e2 e1 -> 
                        P st (f e2 (f_precompute e2) st'))) ->

    (** [f_gt] is OK, i.e. greater elements can be skipped without 
        leaving the equivalence relation. *)
    (forall e1 st, 
        In e1 s -> f_gt e1 (f_precompute e1) st = true ->
        (forall st' e2, P st st' ->
                        In e2 s -> lt e1 e2 -> 
                        P st (f e2 (f_precompute e2) st'))) ->

    (** The base values are in equivalence relation *)
    P i i' ->

    (** The results are in equivalence relation *)
    P (foldWithAbortPrecompute f_precompute f_lt f f_gt s i) (fold f' s i').


(** *** Module Types *)

(** We now define a module type for [foldWithAbort]. This module
    type demands only the existence of the precompute version, since
    the other ones can be easily defined via this most efficient one. *)

Module Type HasFoldWithAbort (E : OrderedType) (Import C : WSetsOnWithDups E).

  Parameter foldWithAbortPrecompute : forall {A B : Type}, 
    foldWithAbortPrecomputeType elt t A B.

  Parameter foldWithAbortPrecomputeSpec : 
     foldWithAbortPrecomputeSpecPred E.lt In (@fold) (@foldWithAbortPrecompute).

End HasFoldWithAbort.


(** ** Derived operations 

    Using these efficient fold operations, many operations can 
    be implemented efficiently. We provide lemmata and efficient implementations
    of useful algorithms via module [HasFoldWithAbortOps]. *)

Module HasFoldWithAbortOps (E : OrderedType) (C : WSetsOnWithDups E)
                           (FT : HasFoldWithAbort E C). 

  Import FT.
  Import C.

  (** *** First lets define the other folding with abort variants *)

  Definition foldWithAbortGtLt {A} f_lt (f : (elt -> A -> A)) f_gt :=
    foldWithAbortPrecompute (fun _ => tt) (fun e _ st => f_lt e st)
      (fun e _ st => f e st) (fun e _ st => f_gt e st).
      
  Lemma foldWithAbortGtLtSpec : 
     foldWithAbortGtLtSpecPred E.lt In (@fold) (@foldWithAbortGtLt).
  Proof.
    rewrite /foldWithAbortGtLt /foldWithAbortGtLtSpecPred.
    intros A i i' f f' f_lt f_gt s P.
    move => H_f_compat H_ff' H_lt H_gt H_ii'.
    apply foldWithAbortPrecomputeSpec => //.
  Qed.


  Definition foldWithAbortGt {A} (f : (elt -> A -> A)) f_gt :=
    foldWithAbortPrecompute (fun _ => tt) (fun _ _ _ => false)
      (fun e _ st => f e st) (fun e _ st => f_gt e st).
      
  Lemma foldWithAbortGtSpec : 
     foldWithAbortGtSpecPred E.lt In (@fold) (@foldWithAbortGt).
  Proof.
    rewrite /foldWithAbortGt /foldWithAbortGtSpecPred.
    intros A i i' f f' f_gt s P.
    move => H_f_compat H_ff' H_gt H_ii'.
    apply foldWithAbortPrecomputeSpec => //.
  Qed.

  Definition foldWithAbort {A} (f : (elt -> A -> A)) f_abort :=
    foldWithAbortPrecompute (fun _ => tt) (fun e _ st => f_abort e st)
      (fun e _ st => f e st) (fun e _ st => f_abort e st).
      
  Lemma foldWithAbortSpec : 
     foldWithAbortSpecPred In (@fold) (@foldWithAbort).
  Proof.
    rewrite /foldWithAbort /foldWithAbortGtSpecPred.
    intros A i i' f f' f_abort s P.
    move => H_equiv_P H_f_compat H_ff' H_abort H_ii'.
    have H_lt_neq: (forall e1 e2, E.lt e1 e2 -> e1 <> e2). {
      move => e1 e2 H_lt H_e12_eq.
      rewrite H_e12_eq in H_lt.
      have : ( Irreflexive E.lt) by apply StrictOrder_Irreflexive.
      rewrite /Irreflexive /Reflexive /complement => H.
      eapply H, H_lt.
    }
    apply foldWithAbortPrecomputeSpec => //; (
      move => e1 st H_in_e1 H_abort_e1 st' e2 H_P H_in_e2 /H_lt_neq H_lt;
      apply (H_abort e1 st H_in_e1 H_abort_e1 st' e2 H_P H_in_e2);
      by auto
    ).
  Qed.


  (** *** Specialisations for equality *)

  (** Let's provide simplified specifications, which use equality instead
      of an arbitrary equivalence relation on results. *)
  Lemma foldWithAbortPrecomputeSpec_Equal : forall (A B : Type) (i : A) (f_pre : elt -> B) 
      (f : elt -> B -> A -> A) (f' : elt -> A -> A) (f_lt f_gt : elt -> B -> A -> bool) (s : t),

      (forall e st, In e s -> (f e (f_pre e) st = f' e st)) ->       

      (* Less is OK *)
      (forall e1 st, 
          In e1 s -> f_lt e1 (f_pre e1) st = true ->
          (forall e2, In e2 s -> E.lt e2 e1 -> 
                      (f e2 (f_pre e2) st = st))) ->

      (* Greater is OK *)
      (forall e1 st, 
          In e1 s -> f_gt e1 (f_pre e1) st = true ->
          (forall e2, In e2 s -> E.lt e1 e2 -> 
                      (f e2 (f_pre e2) st = st))) ->

      (foldWithAbortPrecompute f_pre f_lt f f_gt s i) = (fold f' s i).
  Proof.
    intros A B i f_pre f f' f_lt f_gt s H_f' H_lt H_gt.

     eapply (foldWithAbortPrecomputeSpec A B i i f_pre f f'); eauto. {
       apply eq_equivalence.
     } {
       move => st1 st2 e H_in -> //.
     } {
       move => e1 st H_e1_in H_do_smaller st' e2 <-.
       move : (H_lt e1 st H_e1_in H_do_smaller e2).
       intuition.
     } {
       move => e1 st H_e1_in H_do_greater st' e2 <-.
       move : (H_gt e1 st H_e1_in H_do_greater e2).
       intuition.
     }
  Qed.

  Lemma foldWithAbortGtLtSpec_Equal : forall (A : Type) (i : A) 
      (f : elt -> A -> A) (f' : elt -> A -> A) (f_lt f_gt : elt -> A -> bool) (s : t),

      (forall e st, In e s -> (f e st = f' e st)) ->       

      (* Less is OK *)
      (forall e1 st, 
          In e1 s -> f_lt e1 st = true ->
          (forall e2, In e2 s -> E.lt e2 e1 -> 
                      (f e2 st = st))) ->

      (* Greater is OK *)
      (forall e1 st, 
          In e1 s -> f_gt e1 st = true ->
          (forall e2, In e2 s -> E.lt e1 e2 -> 
                      (f e2 st = st))) ->

      (foldWithAbortGtLt f_lt f f_gt s i) = (fold f' s i).
  Proof.
    intros A i f f' f_lt f_gt s H_f' H_lt H_gt.

     eapply (foldWithAbortGtLtSpec A i i f f'); eauto. {
       apply eq_equivalence.
     } {
       move => st1 st2 e H_in -> //.
     } {
       move => e1 st H_e1_in H_do_smaller st' e2 <-.
       move : (H_lt e1 st H_e1_in H_do_smaller e2).
       intuition.
     } {
       move => e1 st H_e1_in H_do_greater st' e2 <-.
       move : (H_gt e1 st H_e1_in H_do_greater e2).
       intuition.
     }
  Qed.


  Lemma foldWithAbortGtSpec_Equal : forall (A : Type) (i : A) 
      (f : elt -> A -> A) (f' : elt -> A -> A) (f_gt : elt -> A -> bool) (s : t),

      (forall e st, In e s -> (f e st = f' e st)) ->       

      (* Greater is OK *)
      (forall e1 st, 
          In e1 s -> f_gt e1 st = true ->
          (forall e2, In e2 s -> E.lt e1 e2 -> 
                      (f e2 st = st))) ->

      (foldWithAbortGt f f_gt s i) = (fold f' s i).
  Proof.
    intros A i f f' f_gt s H_f' H_gt.

     eapply (foldWithAbortGtSpec A i i f f'); eauto. {
       apply eq_equivalence.
     } {
       move => st1 st2 e H_in -> //.
     } {
       move => e1 st H_e1_in H_do_greater st' e2 <-.
       move : (H_gt e1 st H_e1_in H_do_greater e2).
       intuition.
     }
  Qed.

  Lemma foldWithAbortSpec_Equal : forall (A : Type) (i : A) 
      (f : elt -> A -> A) (f' : elt -> A -> A) (f_abort : elt -> A -> bool) (s : t),

      (forall e st, In e s -> (f e st = f' e st)) ->       

      (* Abort is OK *)
      (forall e1 st, 
          In e1 s -> f_abort e1 st = true ->
          (forall e2, In e2 s -> e1 <> e2 -> 
                      (f e2 st = st))) ->

      (foldWithAbort f f_abort s i) = (fold f' s i).
  Proof.
     intros A i f f' f_abort s H_f' H_abort.

     eapply (foldWithAbortSpec A i i f f'); eauto. {
       apply eq_equivalence.
     } {
       move => st1 st2 e H_in -> //.
     } {
       move => e1 st H_e1_in H_do_abort st' e2 <-.
       move : (H_abort e1 st H_e1_in H_do_abort e2).
       intuition.
     }
  Qed.


  (** *** FoldWithAbortSpecArgs *)

  (** While folding, we are often interested in skipping elements that do not
      satisfy a certain property [P]. This needs expressing in terms of
      skips of smaller of larger elements in order to be done efficiently by
      our folding functions. Formally, this leads to the definition
      of [foldWithAbortSpecForPred]. 

      Given a [FoldWithAbortSpecArg] for a predicate [P] and a
      set [s], many operations can be implemented efficiently. Below we will provide
      efficient versions of [filter], [choose], [exists], [forall] and more.
    *)
  Record FoldWithAbortSpecArg {B} := {
     fwasa_f_pre : (elt -> B);         (** The precompute function *)
     fwasa_f_lt  : (elt -> B -> bool); (** f_lt without state argument *)
     fwasa_f_gt  : (elt -> B -> bool); (** f_gt without state argument *)
     fwasa_P'    : (elt -> B -> bool)  (** the predicate P *) 
  }.

  (** [foldWithAbortSpecForPred s P fwasa] holds, if
      the argument [fwasa] fits the predicate [P] for set [s]. *)
  Definition foldWithAbortSpecArgsForPred {A : Type} 
     (s : t) (P : elt -> bool) (fwasa : @FoldWithAbortSpecArg A) :=

     (** the predicate [P'] coincides for [s] and the given precomputation with [P] *)
     (forall e, In e s -> (fwasa_P' fwasa e (fwasa_f_pre fwasa e) = P e)) /\

     (** If [fwasa_f_lt] holds, all elements smaller than the current one
         don't satisfy predicate P. *)
     (forall e1, 
          In e1 s -> fwasa_f_lt fwasa e1 (fwasa_f_pre fwasa e1) = true ->
          (forall e2, In e2 s -> E.lt e2 e1 -> (P e2 = false))) /\

     (** If [fwasa_f_gt] holds, all elements greater than the current one
         don't satisfy predicate P. *)
     (forall e1, 
          In e1 s -> fwasa_f_gt fwasa e1 (fwasa_f_pre fwasa e1) = true ->
          (forall e2, In e2 s -> E.lt e1 e2 -> (P e2 = false))).
    
   

  (** *** Filter with abort *)
  Definition filter_with_abort {B} (fwasa : @FoldWithAbortSpecArg B) s :=
     @foldWithAbortPrecompute t B (fwasa_f_pre fwasa) (fun e p _ => fwasa_f_lt fwasa e p)
       (fun e e_pre s => if fwasa_P' fwasa e e_pre then add e s else s) 
       (fun e p _ => fwasa_f_gt fwasa e p) s empty.

  Lemma filter_with_abort_spec {B} : forall fwasa P s, 
    @foldWithAbortSpecArgsForPred B s P fwasa ->
    Proper (E.eq ==> Logic.eq) P ->
    Equal (filter_with_abort fwasa s)
          (filter P s).
  Proof.
    unfold foldWithAbortSpecArgsForPred.
    move => [] f_pre f_lt f_gt P' P s /=.
    move => [H_f'] [H_lt] H_gt H_proper.
    rewrite /filter_with_abort /=.

    have -> : (foldWithAbortPrecompute f_pre (fun e p _ => f_lt e p)
     (fun (e : elt) (e_pre : B) (s0 : t) =>
      if P' e e_pre then add e s0 else s0) (fun e p _ => f_gt e p) s empty =
     (fold (fun e s0 => if P e then add e s0 else s0) s empty)). {
      apply foldWithAbortPrecomputeSpec_Equal. {
        intros e st H_e_in.
        rewrite H_f' //.
      } {
        intros e1 st H_e1_in H_f_lt_eq e2 H_e2_in H_lt_e2_e1.
        rewrite (H_f' _ H_e2_in).
        suff -> : (P e2 = false) by done.
        apply (H_lt e1); eauto.
      } {
        intros e1 st H_e1_in H_f_gt_eq e2 H_e2_in H_gt_e2_e1.
        rewrite (H_f' _ H_e2_in).
        suff -> : (P e2 = false) by done.
        apply (H_gt e1); eauto.
      }
    }

    rewrite /Equal => e. 
    rewrite fold_spec. 
    setoid_rewrite filter_spec => //.

    suff -> : forall acc, In e
      (fold_left
         (flip (fun (e0 : elt) (s0 : t) => if P e0 then add e0 s0 else s0))
         (elements s) acc) <-> (InA E.eq e (elements s) /\ P e = true) \/ (In e acc). {
      rewrite elements_spec1.
      suff : (~In e empty) by tauto.
      apply empty_spec.
    }
    induction (elements s) as [| x xs IH] => acc. {
      rewrite /= InA_nil. tauto.
    } {
      rewrite /= /flip IH InA_cons.
      case_eq (P x). {
        rewrite add_spec.
        intuition.
        left.     
        rewrite H0. 
        split => //.
        left.
        apply Equivalence_Reflexive.
      } {
        intuition.
        contradict H2.
        setoid_rewrite H1.
        by rewrite H.
      } 
    }
  Qed. 

  (** *** Choose with abort *)
  Definition choose_with_abort {B} (fwasa : @FoldWithAbortSpecArg B) s :=
     foldWithAbortPrecompute (fwasa_f_pre fwasa) 
       (fun e p st => match st with None => (fwasa_f_lt fwasa e p) | _ => true end)
       (fun e e_pre st => match st with None => 
          if (fwasa_P' fwasa e e_pre) then Some e else None | _ => st end) 

       (fun e p st => match st with None => (fwasa_f_gt fwasa e p) | _ => true end)
       s None.

  Lemma choose_with_abort_spec {B} : forall fwasa P s, 
    @foldWithAbortSpecArgsForPred B s P fwasa ->
    Proper (E.eq ==> Logic.eq) P ->
    (match (choose_with_abort fwasa s) with
       | None => (forall e, In e s -> P e = false)
       | Some e => In e s /\ (P e = true)
     end).
  Proof.
    rewrite /foldWithAbortSpecArgsForPred.
    move => [] f_pre f_lt f_gt P' P s /=.
    move => [H_f'] [H_lt] H_gt H_proper.

    set fwasa := {|
       fwasa_f_pre := f_pre;
       fwasa_f_lt := f_lt;
       fwasa_f_gt := f_gt;
       fwasa_P' := P' |}.

    suff : (match (choose_with_abort fwasa s) with
       | None => (forall e, InA E.eq e (elements s) -> P e = false)
       | Some e => InA E.eq e (elements s) /\ (P e = true)
     end). {
       case (choose_with_abort fwasa s). {
         move => e.
         rewrite elements_spec1 //.
       } {
         move => H e H_in.
         apply H.
         rewrite elements_spec1 //.
       }
    }

    have -> : (choose_with_abort fwasa s =
      (fold (fun e st => 
        match st with 
          | None => if P e then Some e else None 
          | _ => st end) s None)). {
      apply foldWithAbortPrecomputeSpec_Equal. {
        intros e st H_e_in.
        case st => //=.
        rewrite H_f' //.
      } {
        move => e1 [] //= H_e1_in H_f_lt_eq e2 H_e2_in H_lt_e2_e1.
        rewrite (H_f' _ H_e2_in).
        case_eq (P e2) => // H_P_e2.
        contradict H_P_e2.
        apply not_true_iff_false, (H_lt e1); auto.
      } {
        move => e1 [] //= H_e1_in H_f_gt_eq e2 H_e2_in H_gt_e2_e1.
        rewrite (H_f' _ H_e2_in).
        case_eq (P e2) => // H_P_e2.
        contradict H_P_e2.
        apply not_true_iff_false, (H_gt e1); auto.
      }
    }

    rewrite fold_spec /flip.
    induction (elements s) as [| x xs IH]. {
      rewrite /=. 
      move => e /InA_nil //.
    } {
      case_eq (P x) => H_Px; rewrite /= H_Px. {
        have -> : forall xs, fold_left (fun (x0 : option elt) (y : elt) =>
                    match x0 with | Some _ => x0 | None => if P y then Some y else None
                    end) xs (Some x) = Some x. {
          move => ys.
          induction ys => //.
        }
        split; last assumption.
        apply InA_cons_hd.
        apply E.eq_equiv.
      } {
        move : IH.
        case (fold_left
          (fun (x0 : option elt) (y : elt) =>
             match x0 with | Some _ => x0 | None => if P y then Some y else None
             end) xs None). {

             move => e [H_e_in] H_Pe.
             split; last assumption.
             apply InA_cons_tl => //.
        } {
          move => H_e_nin e H_e_in.
          have : (InA E.eq e xs \/ (E.eq e x)). {
            inversion H_e_in; tauto.
          }
          move => []. {
            apply H_e_nin.
          } {
            move => -> //.
          }
        }
      }
    }
  Qed.


  (** *** Exists and Forall with abort *)
  Definition exists_with_abort {B} (fwasa : @FoldWithAbortSpecArg B) s :=
    match choose_with_abort fwasa s with
      | None => false
      | Some _ => true
    end.

  Lemma exists_with_abort_spec {B} : forall fwasa P s, 
    @foldWithAbortSpecArgsForPred B s P fwasa ->
    Proper (E.eq ==> Logic.eq) P ->
    (exists_with_abort fwasa s =
     exists_ P s).
  Proof.
    intros fwasa P s H_fwasa H_proper.
    apply Logic.eq_sym.
    rewrite /exists_with_abort.
    move : (choose_with_abort_spec _ _ _ H_fwasa H_proper).
    case (choose_with_abort fwasa s). {
      move => e [H_e_in] H_Pe.
      rewrite exists_spec /Exists.
      by exists e.
    } {
      move => H_not_ex.
      apply not_true_iff_false.
      rewrite exists_spec /Exists.
      move => [e] [H_in] H_pe.
      move : (H_not_ex e H_in).
      rewrite H_pe //.
    }
  Qed.


  (** Negation leads to forall. *)
  Definition forall_with_abort {B} fwasa s :=
     negb (@exists_with_abort B fwasa s).

  Lemma forall_with_abort_spec {B} : forall fwasa s P, 
    @foldWithAbortSpecArgsForPred B s P fwasa ->
    Proper (E.eq ==> Logic.eq) P ->
    (forall_with_abort fwasa s =
     for_all (fun e => negb (P e)) s).
  Proof.    
    intros fwasa s P H_ok H_proper.
    rewrite /forall_with_abort exists_with_abort_spec; auto.

    rewrite eq_iff_eq_true negb_true_iff -not_true_iff_false.
    rewrite exists_spec. 
    setoid_rewrite for_all_spec; last solve_proper.

    rewrite /Exists /For_all.
    split. {
      move => H_pre x H_x_in.
      rewrite negb_true_iff -not_true_iff_false => H_Px.
      apply H_pre.
      by exists x.
    } {
      move => H_pre [x] [H_x_in] H_P_x.
      move : (H_pre x H_x_in).
      rewrite H_P_x.
      done.
    }
  Qed.

End HasFoldWithAbortOps.



(** ** Modules Types For Sets with Fold with Abort *)
Module Type WSetsWithDupsFoldA.
  Declare Module E : OrderedType.
  Include WSetsOnWithDups E.
  Include HasFoldWithAbort E.
  Include HasFoldWithAbortOps E.
End WSetsWithDupsFoldA.

Module Type WSetsWithFoldA <: WSets.
  Declare Module E : OrderedType.
  Include WSetsOn E.
  Include HasFoldWithAbort E.
  Include HasFoldWithAbortOps E.
End WSetsWithFoldA.

Module Type SetsWithFoldA <: Sets.
  Declare Module E : OrderedType.
  Include SetsOn E.
  Include HasFoldWithAbort E.
  Include HasFoldWithAbortOps E.
End SetsWithFoldA.


(** ** Implementations *)

(** *** GenTree implementation 
    Finally, provide such a fold with abort operation for generic trees. *)
Module MakeGenTreeFoldA (Import E : OrderedType) (Import I:InfoTyp) 
  (Import Raw:Ops E I)
  (M : MSetGenTree.Props E I Raw).

  Fixpoint foldWithAbort_Raw {A B: Type} (f_pre : E.t -> B) f_lt (f: E.t -> B -> A -> A) f_gt t (base: A) : A :=
    match t with
    | Raw.Leaf => base
    | Raw.Node _ l x r =>
        let x_pre := f_pre x in 
        let st0 := if f_lt x x_pre base then base else foldWithAbort_Raw f_pre f_lt f f_gt l base in 
        let st1 := f x x_pre st0 in
        let st2 := if f_gt x x_pre st1 then st1 else foldWithAbort_Raw f_pre f_lt f f_gt r st1 in 
        st2
    end.

  Lemma foldWithAbort_RawSpec : forall (A B : Type) (i i' : A) (f_pre : E.t -> B) 
      (f : E.t -> B -> A -> A) (f' : E.t -> A -> A) (f_lt f_gt : E.t -> B -> A -> bool) (s : Raw.tree)
      (P : A -> A -> Prop),

      (M.bst s) ->
      Equivalence P ->
      (forall st st' e, M.In e s -> P st st' -> P (f e (f_pre e) st) (f e (f_pre e) st')) ->
      (forall e st, M.In e s -> P (f e (f_pre e) st) (f' e st)) ->       

      (* Less is OK *)
      (forall e1 st, 
          M.In e1 s -> f_lt e1 (f_pre e1) st = true ->
          (forall st' e2, P st st' ->
                          M.In e2 s -> E.lt e2 e1 -> 
                          P st (f e2 (f_pre e2) st'))) ->

      (* Greater is OK *)
      (forall e1 st, 
          M.In e1 s -> f_gt e1 (f_pre e1) st = true ->
          (forall st' e2, P st st' ->
                          M.In e2 s -> E.lt e1 e2 -> 
                          P st (f e2 (f_pre e2) st'))) ->

      P i i' ->
      P (foldWithAbort_Raw f_pre f_lt f f_gt s i) (fold f' s i').
   Proof.
     intros A B i i' f_pre f f' f_lt f_gt s P.
     move => H_bst H_equiv_P H_P_f H_f' H_RL H_RG.

     set base := s.

     move : i i'.
     have : (forall e, M.In e base -> M.In e s). {
       rewrite /In /base //.
     }
     have : M.bst base. {
       apply H_bst.
     }
     move : base.
     clear H_bst.

     induction base as [|c l IHl e r IHr] using M.tree_ind. {
       rewrite /foldWithAbort_Raw /Raw.fold.
       move => _ _ i i' //.
     } {
       move => H_bst H_sub i i' H_P_ii'.

       have [H_bst_l [H_bst_r [H_lt_tree_l H_gt_tree_r]]]: 
         M.bst l /\ M.bst r /\ M.lt_tree e l /\ M.gt_tree e r. {
         inversion H_bst. done.
       }
       
       have H_sub_l : (forall e0 : E.t, M.In e0 l -> M.In e0 s /\ E.lt e0 e). {
         intros e0 H_in_l.
         split; last by apply H_lt_tree_l. 
         eapply H_sub.
         rewrite /M.In M.In_node_iff.
         tauto.
       }
       move : (IHl H_bst_l) => {IHl} IHl {H_bst_l} {H_lt_tree_l}.
       have H_sub_r : (forall e0 : E.t, M.In e0 r -> M.In e0 s /\ E.lt e e0). {
         intros e0 H_in_r.
         split; last by apply H_gt_tree_r. 
         eapply H_sub.
         rewrite /M.In M.In_node_iff.
         tauto.
       }
       move : (IHr H_bst_r) => {IHr} IHr {H_bst_r} {H_gt_tree_r}.
       have H_in_e : M.In e s. {
         eapply H_sub.
         rewrite /M.In M.In_node_iff.
         right; left.
         apply Equivalence_Reflexive.
       }
       move => {H_sub}.

       rewrite /=.
       set st0 := if f_lt e (f_pre e) i then i else foldWithAbort_Raw f_pre f_lt f f_gt l i.
       set st0' := Raw.fold f' l i'.
       set st1 := f e (f_pre e) st0.
       set st1' := f' e st0'.
       set st2 := if f_gt e (f_pre e) st1 then st1 else foldWithAbort_Raw f_pre f_lt f f_gt r st1.
       set st2' := Raw.fold f' r st1'.

       have H_P_st0 : P st0 st0'. {
         rewrite /st0 /st0'.
         case_eq (f_lt e (f_pre e) i). {
           move => H_fl_eq.
           move :  H_P_ii' H_sub_l.
           move :  H_equiv_P H_f' (H_RL _ _ H_in_e H_fl_eq).
           rewrite /M.lt_tree. clear.
           move => H_equiv_P H_f' H_RL.
           move : i'.
           induction l as [|c l IHl e' r IHr] using M.tree_ind. {
             done.
           } {
             intros i' H_P_ii' H_sub_l.
             rewrite /=.
             apply IHr; last first. {
               move => y H_y_in. 
               apply H_sub_l.
               rewrite /M.In M.In_node_iff. tauto.
             }
             have [] : (M.In e' s /\ E.lt e' e). {
               apply H_sub_l.
               rewrite /M.In M.In_node_iff. 
               right; left.
               apply Equivalence_Reflexive.
             }
             move => H_e'_in H_lt_in.
             suff H_P_i : (P i (f e' (f_pre e') (fold f' l i'))). {
               eapply Equivalence_Transitive; first apply H_P_i.
               by apply H_f'.
             }
             eapply H_RL => //.
             apply IHl; last first. {
               move => y H_y_in. 
               apply H_sub_l.
               rewrite /M.In M.In_node_iff. tauto.
             }
             assumption.
           }
         } {
           move => _.
           apply IHl => //.
           eapply H_sub_l.
         }
       }
       have H_P_st1 : P st1 st1'. {
         rewrite /st1 /st1'.
         rewrite -H_f' //.
         apply H_P_f => //.
       }
       have H_P_st2 : P st2 st2'. {
         rewrite /st2 /st2'.
         clearbody st1 st1'.
         case_eq (f_gt e (f_pre e) st1). {
           move => H_gt_eq.
           move :  H_P_st1 H_sub_r.
           move : H_equiv_P (H_RG _ _ H_in_e H_gt_eq) H_f'.
           unfold M.gt_tree. clear.
           move => H_equiv_P H_RG H_f'.
           move : st1'.
           induction r as [|c l IHl e' r IHr] using M.tree_ind. {
             done. 
           } {
             intros st1' H_P_st1 H_sub_r.
             rewrite /=.
             apply IHr; last first. {
               move => y H_y_in. 
               apply H_sub_r.
               rewrite /M.In M.In_node_iff. tauto.
             }
             have [] : (M.In e' s /\ E.lt e e'). {
               apply H_sub_r.
               rewrite /M.In M.In_node_iff. 
               right; left.
               apply Equivalence_Reflexive.
             }
             move => H_e'_in H_lt_ee'.
             suff H_P_st1_aux : (P st1 (f e' (f_pre e') (fold f' l st1'))). {
               eapply Equivalence_Transitive; first apply H_P_st1_aux.
               by apply H_f'.
             }
             eapply H_RG => //.
             apply IHl; last first. {
               move => y H_y_in. 
               apply H_sub_r.
               rewrite /M.In M.In_node_iff. tauto.
             }
             assumption.
           }
         } {
           move => _.
           apply IHr => //.
           eapply H_sub_r.
         }
       }
       done.
     }
  Qed.
End MakeGenTreeFoldA.


(** *** AVL implementation 
    The generic tree implementation naturally leads to an AVL one. *)

Module MakeAVLSetsWithFoldA (X : OrderedType) <: SetsWithFoldA with Module E := X.
  Include MSetAVL.Make X.
  Include MakeGenTreeFoldA X Z_as_Int Raw Raw.

  Definition foldWithAbortPrecompute {A B: Type} f_pre f_lt (f: elt -> B -> A -> A) f_gt t (base: A) : A :=
    foldWithAbort_Raw f_pre f_lt f f_gt (t.(this)) base.

  Lemma foldWithAbortPrecomputeSpec : foldWithAbortPrecomputeSpecPred X.lt In fold (@foldWithAbortPrecompute).
  Proof.
    intros A B i i' f_pre f f' f_lt f_gt s P.
    move => H_P_f H_f' H_RL H_RG H_P_ii'.

    rewrite /foldWithAbortPrecompute /fold.
    apply foldWithAbort_RawSpec => //.
    case s. rewrite /this /Raw.Ok //.
  Qed.
 
  Include HasFoldWithAbortOps X.

End MakeAVLSetsWithFoldA.


(** *** RBT implementation 
    The generic tree implementation naturally leads to an RBT one. *)
Module MakeRBTSetsWithFoldA (X : OrderedType) <: SetsWithFoldA with Module E := X.
  Include MSetRBT.Make X.
  Include MakeGenTreeFoldA X Color Raw Raw.

  Definition foldWithAbortPrecompute {A B: Type} f_pre f_lt (f: elt -> B -> A -> A) f_gt t (base: A) : A :=
    foldWithAbort_Raw f_pre f_lt f f_gt (t.(this)) base.

  Lemma foldWithAbortPrecomputeSpec : foldWithAbortPrecomputeSpecPred X.lt In fold (@foldWithAbortPrecompute).
  Proof.
    intros A B i i' f_pre f f' f_lt f_gt s P.
    move => H_P_f H_f' H_RL H_RG H_P_ii'.

    rewrite /foldWithAbortPrecompute /fold.
    apply foldWithAbort_RawSpec => //.
    case s. rewrite /this /Raw.Ok //.
  Qed.
 
  Include HasFoldWithAbortOps X.

End MakeRBTSetsWithFoldA.


(** ** Sorted Lists Implementation *)
Module MakeListSetsWithFoldA (X : OrderedType) <: SetsWithFoldA with Module E := X.
  Include MSetList.Make X.

  Fixpoint foldWithAbortRaw {A B: Type} (f_pre : X.t -> B) (f_lt : X.t -> B -> A -> bool) 
    (f: X.t -> B -> A -> A) (f_gt : X.t -> B -> A -> bool) (t : list X.t) (acc : A) : A :=
  match t with
    | nil => acc
    | x :: xs => (
        let pre_x := f_pre x in
        let acc := f x (pre_x) acc in
        if (f_gt x pre_x acc) then
          acc
        else 
          foldWithAbortRaw f_pre f_lt f f_gt xs acc 
      )
  end.

  Definition foldWithAbortPrecompute {A B: Type} f_pre f_lt f f_gt t acc :=
    @foldWithAbortRaw A B f_pre f_lt f f_gt t.(this) acc.

  Lemma foldWithAbortPrecomputeSpec : foldWithAbortPrecomputeSpecPred X.lt In fold (@foldWithAbortPrecompute).
  Proof.
    intros A B i i' f_pre f f' f_lt f_gt.
    move => [] l H_is_ok_l P H_equiv_P.
    rewrite /fold /foldWithAbortPrecompute /In /this /Raw.In /Raw.fold.
    move => H_P_f H_f' H_RL H_RG.

    set base := l.
    move : i i'.
    have : (forall e, InA X.eq e base -> InA X.eq e l). {
      rewrite /base //.
    }
    have : sort X.lt base. {
      rewrite Raw.isok_iff /base //.
    }
    clear H_is_ok_l.

    induction base as [| x xs IH]. {
      by simpl.
    }
    move => H_sort H_in_xxs i i' Pii' /=.

    have [H_sort_xs H_hd_rel {H_sort}] : Sorted X.lt xs /\ HdRel X.lt x xs. {
      by inversion H_sort.
    }

    move : H_hd_rel.
    rewrite (Raw.ML.Inf_alt x H_sort_xs) => H_lt_xs.

    have H_x_in_l : InA X.eq x l. {
      apply H_in_xxs.
      apply InA_cons_hd.
      apply X.eq_equiv.
    } 
    have H_in_xs : (forall e : X.t, InA X.eq e xs -> InA X.eq e l). {
      intros e H_in.
      apply H_in_xxs, InA_cons_tl => //.
    }
   
    have H_P_next : P (f x (f_pre x) i) (flip f' i' x). {
      rewrite /flip -H_f' //.
      apply H_P_f => //.
    }

    case_eq (f_gt x (f_pre x) (f x (f_pre x) i)); last first. {
      move => _.
      apply IH => //.
    } {
      move => H_gt.
      suff H_suff : (forall st, P (f x (f_pre x) i) st -> 
         P (f x (f_pre x) i) (fold_left (flip f') xs st)). {
         apply H_suff => //.
      }
      move : H_in_xs H_lt_xs.

      clear IH H_in_xxs H_sort_xs.
      move : (H_RG x _ H_x_in_l H_gt) => H_RG_x.
      induction xs as [| x' xs' IH']. {
        done.
      } {
        intros H_in_xs H_lt_xs st H_P_st.
        rewrite /=.
        have H_x'_in_l : InA X.eq x' l. {
          apply H_in_xs.
          apply InA_cons_hd, X.eq_equiv.
        } 
        apply IH'. {
          intros e H.
          apply H_in_xs, InA_cons_tl => //.
        } {
          intros e H.
          apply H_lt_xs, InA_cons_tl => //.
        } {
          rewrite /flip -H_f' //.
          apply H_RG_x => //.
          apply H_lt_xs.
          apply InA_cons_hd, X.eq_equiv.
        }
      }
    }
  Qed.
 
  Include HasFoldWithAbortOps X.

End MakeListSetsWithFoldA.


(** *** Unsorted Lists without Dups Implementation *)
Module MakeWeakListSetsWithFoldA (X : OrderedType) <: WSetsWithFoldA with Module E := X.
  Module Raw := MSetWeakList.MakeRaw X.
  Module E := X.
  Include WRaw2SetsOn E Raw.

  Fixpoint foldWithAbortRaw {A B: Type} (f_pre : X.t -> B) (f_lt : X.t -> B -> A -> bool) 
    (f: X.t -> B -> A -> A) (f_gt : X.t -> B -> A -> bool) (t : list X.t) (acc : A) : A :=
  match t with
    | nil => acc
    | x :: xs => (
        let pre_x := f_pre x in
        let acc := f x (pre_x) acc in
        if (f_gt x pre_x acc) && (f_lt x pre_x acc) then
          acc
        else
          foldWithAbortRaw f_pre f_lt f f_gt xs acc 
      )
  end.

  Definition foldWithAbortPrecompute {A B: Type} f_pre f_lt f f_gt t acc :=
    @foldWithAbortRaw A B f_pre f_lt f f_gt t.(this) acc.

  Lemma foldWithAbortPrecomputeSpec : foldWithAbortPrecomputeSpecPred X.lt In fold (@foldWithAbortPrecompute).
  Proof.
    intros A B i i' f_pre f f' f_lt f_gt.
    move => [] l H_is_ok_l P H_P_equiv.
    rewrite /fold /foldWithAbortPrecompute /In /this /Raw.In /Raw.fold.
    move => H_P_f H_f' H_RL H_RG.

    set base := l.
    move : i i'.
    have : (forall e, InA X.eq e base -> InA X.eq e l). {
      rewrite /base //.
    }
    have : NoDupA X.eq base. {
      apply H_is_ok_l.
    }
    clear H_is_ok_l.

    induction base as [| x xs IH]. {
      by simpl.
    }
    move => H_nodup_xxs H_in_xxs i i' Pii' /=.

    have [H_nin_x_xs H_nodup_xs {H_nodup_xxs}] : ~ InA X.eq x xs /\ NoDupA X.eq xs. {
      by inversion H_nodup_xxs.
    }

    have H_x_in_l : InA X.eq x l. {
      apply H_in_xxs.
      apply InA_cons_hd.
      apply X.eq_equiv.
    } 
    have H_in_xs : (forall e : X.t, InA X.eq e xs -> InA X.eq e l). {
      intros e H_in.
      apply H_in_xxs, InA_cons_tl => //.
    }
   
    have H_P_next : P (f x (f_pre x) i) (flip f' i' x). {
      rewrite /flip -H_f' //.
      apply H_P_f => //.
    }

    case_eq (f_gt x (f_pre x) (f x (f_pre x) i) &&
             f_lt x (f_pre x) (f x (f_pre x) i)); last first. {
      move => _.
      apply IH => //.
    } {
      move => /andb_true_iff [H_gt H_lt].
      suff H_suff : (forall st, P (f x (f_pre x) i) st -> 
         P (f x (f_pre x) i) (fold_left (flip f') xs st)). {
         apply H_suff => //.
      }

      have H_neq_xs : forall e, List.In e xs -> X.lt x e \/ X.lt e x. {
        intros e H_in.

        move : (X.compare_spec x e).
        case (X.compare x e) => H_cmp; inversion H_cmp. {
          contradict H_nin_x_xs.
          rewrite InA_alt.
          by exists e. 
        } {
          by left.
        } {
          by right.
        }
      }
      move : H_in_xs H_neq_xs.

      clear IH H_in_xxs H_nodup_xs.
      move : (H_RG x _ H_x_in_l H_gt) => H_RG_x.
      move : (H_RL x _ H_x_in_l H_lt) => H_RL_x.
      induction xs as [| x' xs' IH']. {
        done.
      } {
        intros H_in_xs H_neq_xs st H_P_st.
        rewrite /=.
        have H_x'_in_xxs' : List.In x' (x' :: xs'). {
          simpl; by left.
        } 
        have H_x'_in_l : InA X.eq x' l. {
          apply H_in_xs.
          apply InA_cons_hd, X.eq_equiv.
        } 
        apply IH'. {
          intros H.
          apply H_nin_x_xs, InA_cons_tl => //.
        } {
          intros e H.
          apply H_in_xs, InA_cons_tl => //.
        } {
          intros e H.
          apply H_neq_xs, in_cons => //.
        } {
          rewrite /flip -H_f' //.
          move : (H_neq_xs x' H_x'_in_xxs') => [] H_cmp. {
            apply H_RG_x => //.
          } {
            apply H_RL_x => //.
          }
        }
      }
    }
  Qed.
 
  Include HasFoldWithAbortOps X.

End MakeWeakListSetsWithFoldA.

