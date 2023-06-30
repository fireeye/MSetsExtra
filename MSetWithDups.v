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

(** * Signature for weak sets which may contain duplicates

    The interface [WSetsOn] demands that [elements] returns a list
    without duplicates and that the fold function iterates over this
    result. Another potential problem is that the function [cardinal]
    is supposed to return the length of the elements list.

    Therefore, implementations that store duplicates internally and for
    which the fold function would visit elements multiple times are
    ruled out.  Such implementations might be desirable for performance
    reasons, though. One such (sometimes useful) example are unsorted
    lists with duplicates. They have a very efficient insert and union
    operation. If they are used in such a way that not too many
    membership tests happen and that not too many duplicates
    accumulate, it might be a very efficient datastructure.

    In order to allow efficient weak set implementations that use
    duplicates internally, we provide new module types in this
    file. There is [WSetsOnWithDups], which is a proper subset of
    [WSetsOn]. It just removes the problematic properties of [elements]
    and [cardinal].

    Since one is of course interested in specifying the cardinality
    and in computing a list of elements without duplicates, there is
    also an extension [WSetsOnWithDupsExtra] of [WSetsOnWithDups]. This
    extension introduces a new operation [elements_dist], which is a
    version of [elements] without duplicates. This allows to
    specify [cardinality] with respect to [elements_dist].
*)

Require Import Coq.MSets.MSetInterface.
Require Import mathcomp.ssreflect.ssreflect.

(** ** WSetsOnWithDups

    The module type [WSetOnWithDups] is a proper subset of [WSetsOn];
    the problematic parameters [cardinal_spec] and [elements_spec2w]
    are missing. 

    We use this approach to be as noninvasive as possible. If we had the
    liberty to modify the existing MSet library, it might be better to
    define WSetsOnWithDups as below and define WSetOn by adding the two
    extra parameters.
 *)
Module Type WSetsOnWithDups (E : DecidableType).
  Include WOps E.

  Parameter In : elt -> t -> Prop.
  #[local] Declare Instance In_compat : Proper (E.eq==>eq==>iff) In.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
  Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

  Definition eq : t -> t -> Prop := Equal.
  Include IsEq. (** [eq] is obviously an equivalence, for subtyping only *)
  Include HasEqDec.

  Section Spec.
  Variable s s': t.
  Variable x y : elt.
  Variable f : elt -> bool.
  Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

  Parameter mem_spec : mem x s = true <-> In x s.
  Parameter equal_spec : equal s s' = true <-> s[=]s'.
  Parameter subset_spec : subset s s' = true <-> s[<=]s'.
  Parameter empty_spec : Empty empty.
  Parameter is_empty_spec : is_empty s = true <-> Empty s.
  Parameter add_spec : In y (add x s) <-> E.eq y x \/ In y s.
  Parameter remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
  Parameter singleton_spec : In y (singleton x) <-> E.eq y x.
  Parameter union_spec : In x (union s s') <-> In x s \/ In x s'.
  Parameter inter_spec : In x (inter s s') <-> In x s /\ In x s'.
  Parameter diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
  Parameter fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
    fold f s i = fold_left (flip f) (elements s) i.
  Parameter filter_spec : compatb f ->
    (In x (filter f s) <-> In x s /\ f x = true).
  Parameter for_all_spec : compatb f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Parameter exists_spec : compatb f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Parameter partition_spec1 : compatb f ->
    fst (partition f s) [=] filter f s.
  Parameter partition_spec2 : compatb f ->
    snd (partition f s) [=] filter (fun x => negb (f x)) s.
  Parameter elements_spec1 : InA E.eq x (elements s) <-> In x s.
  Parameter choose_spec1 : choose s = Some x -> In x s.
  Parameter choose_spec2 : choose s = None -> Empty s.

  End Spec.

End WSetsOnWithDups.


(** ** WSetsOnWithDupsExtra

    [WSetsOnWithDupsExtra] introduces [elements_dist] in order to
    specify cardinality and in order to get an operation similar to
    the original behavior of [elements]. *)
Module Type WSetsOnWithDupsExtra (E : DecidableType).  
  Include WSetsOnWithDups E.
  
  (** An operation for getting an elements list without duplicates *)
  Parameter elements_dist : t -> list elt.
  
  Parameter elements_dist_spec1 : forall x s, InA E.eq x (elements_dist s) <->
                                              InA E.eq x (elements s).

  Parameter elements_dist_spec2w : forall s, NoDupA E.eq (elements_dist s).


  (** Cardinality can then be specified with respect to [elements_dist]. *)
  Parameter cardinal_spec : forall s, cardinal s = length (elements_dist s).
End WSetsOnWithDupsExtra.


(** ** WSetOn to WSetsOnWithDupsExtra

    Since [WSetsOnWithDupsExtra] is morally a weaker version of [WSetsOn]
    that allows the fold operation to visit elements multiple time, we can write then
    following conversion. *)

Module WSetsOn_TO_WSetsOnWithDupsExtra (E : DecidableType) (W : WSetsOn E) <: 
  WSetsOnWithDupsExtra E. 

  Include W.
  
  Definition elements_dist := W.elements.

  Lemma elements_dist_spec1 : forall x s, InA E.eq x (elements_dist s) <->
                                          InA E.eq x (elements s).
  Proof. done. Qed.

  Lemma elements_dist_spec2w : forall s, NoDupA E.eq (elements_dist s).
  Proof. apply elements_spec2w. Qed.

End WSetsOn_TO_WSetsOnWithDupsExtra.


