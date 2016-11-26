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

(* CHANGES
 *
 * 25-09-2016 Thomas Tuerk <thomas@tuerk-brechen.de>
 *   implement union, inter, diff, subset, choose efficiently
 * 03-10-2016 Thomas Tuerk <thomas@tuerk-brechen.de>
 *   implement fold, exists_, for_all, filter, partition efficiently
 *)

(** * Weak sets implemented by interval lists 

    This file contains an implementation of the set interface
    [SetsOn] which uses internally intervals of Z. This allows some
    large sets, which naturally map to intervals of integers to be
    represented very efficiently.

    Internally intervals of Z are used. However, via an encoding
    and decoding layer, other types of elements can be handled as
    well. There are instantiations for Z, N and nat currently.
    More can be easily added.
*)

Require Import MSetInterface OrdersFacts OrdersLists.
Require Import BinNat.
Require Import mathcomp.ssreflect.ssreflect.
Require Import NArith.
Require Import ZArith.
Require Import NOrder.
Require Import DecidableTypeEx.
Module Import NOP := NOrderProp N.
Open Scope Z_scope.

(** ** Auxiliary stuff *)

(** Simple auxiliary lemmata *)
Lemma Z_le_add_r : forall (z : Z) (n : N),
  z <= z + Z.of_N n.
Proof.
  intros z n.
  suff : (z + 0 <= z + Z.of_N n). {
    rewrite Z.add_0_r //.
  }
  apply Zplus_le_compat_l.
  apply N2Z.is_nonneg.
Qed.

Lemma Z_lt_add_r : forall (z : Z) (n : N),
  (n <> 0)%N ->
  z < z + Z.of_N n.
Proof.
  move => z n H_neq_0.
  suff : (z + Z.of_N 0 < z + Z.of_N n). {
    rewrite Z.add_0_r //.
  }
  apply Z.add_lt_mono_l, N2Z.inj_lt.
  by apply N.neq_0_lt_0.
Qed.

Lemma Z_lt_le_add_r : forall y1 y2 c, 
  y1 < y2 ->
  y1 <= y2 + Z.of_N c.
Proof.
  intros y1 y2 c H.
  apply Z.le_trans with (m := y2). {
    by apply Z.lt_le_incl.
  } {
    apply Z_le_add_r.
  }
Qed.

Lemma Z_to_N_minus_neq_0 : forall (x y : Z),
    y < x ->
    Z.to_N (x - y) <> 0%N.
Proof.
  intros x y H_y_lt.
  apply N.neq_0_lt_0.
  apply N2Z.inj_lt.
  suff H :  0 < x - y. {
    rewrite Z2N.id => //.
    by apply Z.lt_le_incl.
  }
  by apply Z.lt_0_sub.
Qed.

Lemma add_add_sub_eq : forall (x y : Z), (x + (y - x) = y). 
Proof.
  intros x y.
  rewrite Z.add_sub_assoc => //.
  rewrite  Z.add_sub_swap Z.sub_diag Z.add_0_l //.
Qed.

Lemma NoDupA_map {A B} : forall (eqA : A -> A -> Prop) (eqB : B -> B -> Prop) (f : A -> B) l,
  NoDupA eqA l ->
  (forall x1 x2,  List.In x1 l -> List.In x2 l ->
                  eqB (f x1) (f x2) -> eqA x1 x2) ->
  NoDupA eqB (map f l).
Proof.
  intros eqA eqB f.
  induction l as [| x xs IH]. {
    move => _ _; rewrite /=.
    apply NoDupA_nil.
  } {
    move => H_pre H_eqA_impl.
    have [H_nin_x H_no_dup_xs] : ~ InA eqA x xs /\ NoDupA eqA xs. {
      by inversion_clear H_pre.
    }
    simpl.
    apply NoDupA_cons; last first. {
      apply IH => //.
      intros x1 x2 H_in_x1 H_in_x2 H_eqB.
      apply H_eqA_impl => //=; by right.
    }
    move => H_in_map; apply H_nin_x.
    move : H_in_map.
    rewrite !InA_alt => [[y] [H_eqB_y]].
    rewrite in_map_iff => [[y'] [H_y_eq] H_y'_in].
    subst.
    exists y'.
    split => //.
    apply H_eqA_impl => //. {
      by simpl; left.
    } {
      by simpl; right.
    }
  }
Qed.


(** *** rev_map 

    rev_map is used for efficiency. *)
Fixpoint rev_map_aux {A B} (f : A -> B) (acc : list B) (l : list A) :=
  match l with
   | nil => acc
   | x :: xs => rev_map_aux f ((f x)::acc) xs
  end.

Definition rev_map {A B} (f : A -> B) (l : list A) : list B := rev_map_aux f nil l.


(** Lemmata about rev_map *)
Lemma rev_map_aux_alt_def {A B} : forall (f : A -> B) l acc,
  rev_map_aux f acc l = List.rev_append (List.map f l) acc. 
Proof.
  intro f.
  induction l as [| x xs IH]. {
    intros acc.
    by simpl.
  } {
    intros acc.
    rewrite /= IH //.
  }
Qed.

Lemma rev_map_alt_def {A B} : forall (f : A -> B) l,
  rev_map f l = List.rev (List.map f l). 
Proof.
  intros f l.
  rewrite /rev_map rev_map_aux_alt_def -rev_alt //.
Qed.


(** ** Encoding Elements *)

(** We want to encode not only elements of type Z, but other types
    as well. In order to do so, an encoding / decoding layer is used.
    This layer is represented by module type [ElementEncode]. It
    provides encode and decode function. *)

Module Type ElementEncode.
  Declare Module E : OrderedType.

  Parameter encode : E.t -> Z.
  Parameter decode : Z -> E.t.

  (** Decoding is the inverse of encoding. Notice that
      the reverse is not demanded. This means that
      we do need to provide for all integers [z] an
      element [e] with [encode v = z]. *)
  Axiom decode_encode_ok: forall (e : E.t),
    decode (encode e) = e.

  (** Encoding is compatible with the equality of elements. *)
  Axiom encode_eq : forall (e1 e2 : E.t),
    (Z.eq (encode e1) (encode e2)) <-> E.eq e1 e2.

  (** Encoding is compatible with the order of elements. *)
  Axiom encode_lt : forall (e1 e2 : E.t),
    (Z.lt (encode e1) (encode e2)) <-> E.lt e1 e2.
                                      
End ElementEncode.


(** ** Set Operations 

    We represent sets of Z via lists of intervals. The intervals are all
    in increasing order and non-overlapping. Moreover, we require the most compact
    representation, i.e. no two intervals can be merged. For example

    [0-2, 4-4, 6-8] is a valid interval list for the set {0;1;2;4;6;7;8}

    In contrast

    [4-4, 0-2, 6-8] is a invalid because the intervals are not ordered andb
    [0-2, 4-5, 6-8] is a invalid because it is not compact ([0-2, 4--8] is valid).


    Intervals we represent by tuples [(Z, N)]. The tuple [(z, c)]  represents the
    interval [z-(z+c)].

    We apply the encode function before adding an element to such interval sets and
    the decode function when checking it. This allows for sets with other element types
    than Z.
 *)
Module Ops (Enc : ElementEncode) <: Ops Enc.E.
  Definition elt := Enc.E.t.
  Definition t := list (Z * N).

  (** The empty list is trivial to define and check for. *)
  Definition empty : t := nil.
  Definition is_empty (l : t) := match l with nil => true | _ => false end.

 
  (** Defining the list of elements, is much more tricky, especially, 
      if it needs to be executable. *) 
  Lemma acc_pred : forall n p, n = Npos p -> Acc N.lt n -> Acc N.lt (N.pred n).
  Proof.
    intros n p H0 H1.
    apply H1.
    rewrite H0.
    apply N.lt_pred_l.
    discriminate.
  Defined.
 
  Fixpoint fold_elementsZ_aux {A} (f : A -> Z -> option A) (acc : A) (x : Z) (c : N) (H : Acc N.lt c) { struct H } : (bool * A) :=
    match c as c0 return c = c0 -> (bool * A) with
    | N0 => fun _ => (false, acc)
    | c => fun Heq => match (f acc x) with
        | None => (true, acc)
        | Some acc' =>             
          fold_elementsZ_aux f acc' (Z.succ x) (N.pred c) (acc_pred _ _ Heq H) end
    end (refl_equal _).

  Definition fold_elementsZ_single {A} f (acc : A) x c := fold_elementsZ_aux f acc x c (lt_wf_0 _).

  Fixpoint fold_elementsZ {A} f (acc : A) (s : t) : (bool * A) := 
    match s with 
    | nil => (false, acc)
    | (x, c) :: s' =>
      match fold_elementsZ_single f acc x c with
          (false, acc') => fold_elementsZ f acc' s'
        | (true, acc') => (true, acc')
      end
    end.

  Definition elementsZ (s : t) : list Z := 
    snd (fold_elementsZ (fun l x => Some (x :: l)) nil s).

  Definition elements (s : t) : list elt := 
    rev_map Enc.decode (elementsZ s).   
  
  (** membership is easily defined *)
  Fixpoint memZ (x : Z) (s : t) :=
    match s with
    | nil => false
    | (y, c) :: l =>
        if (Z.ltb x y) then false else
        if (Z.ltb x (y+Z.of_N c)) then true else
        memZ x l
    end.

  Definition mem (x : elt) (s : t) := memZ (Enc.encode x) s.

  (** Comparing intervals *)
  Inductive interval_compare_result := 
      ICR_before
    | ICR_before_touch
    | ICR_overlap_before 
    | ICR_overlap_after
    | ICR_equal
    | ICR_subsume_1
    | ICR_subsume_2
    | ICR_after
    | ICR_after_touch.

  Definition interval_compare (i1 i2 : (Z * N)) : interval_compare_result := 
    match (i1, i2) with ((y1, c1), (y2, c2)) => 
      let yc2 := (y2+Z.of_N c2) in
      match (Z.compare yc2 y1) with
        | Lt => ICR_after
        | Eq => ICR_after_touch
        | Gt => let yc1 := (y1+Z.of_N c1) in
                match (Z.compare yc1 y2) with
                | Lt => ICR_before
                | Eq => ICR_before_touch
                | Gt => (* y2 < y1+c1 /\ y1 < y2 + c2 *)
                        match (Z.compare y1 y2, Z.compare yc1 yc2) with
                        | (Lt, Lt) => ICR_overlap_before
                        | (Lt, _) => ICR_subsume_2
                        | (Eq, Lt) => ICR_subsume_1
                        | (Eq, Gt) => ICR_subsume_2
                        | (Eq, Eq) => ICR_equal
                        | (Gt, Gt) => ICR_overlap_after
                        | (Gt, _) => ICR_subsume_1
                        end
                end
      end
    end.

  Definition interval_1_compare (y1 : Z) (i : (Z * N)) : interval_compare_result := 
    match i with (y2, c2) => 
      let yc2 := (y2+Z.of_N c2) in
      match (Z.compare yc2 y1) with
        | Lt => ICR_after
        | Eq => ICR_after_touch
        | Gt => match (Z.compare (Z.succ y1) y2) with
                | Lt => ICR_before 
                | Eq => ICR_before_touch
                | Gt => ICR_subsume_1
                end
      end
    end.

  Fixpoint compare (s1 s2 : t) :=
    match (s1, s2) with
      | (nil, nil) => Eq
      | (nil, _ :: _) => Lt
      | (_ :: _, nil) => Gt
      | ((y1, c1)::s1', (y2, c2)::s2') =>
        match (Z.compare y1 y2) with
          | Lt => Lt
          | Gt => Gt
          | Eq => match N.compare c1 c2 with
                    | Lt => Lt
                    | Gt => Gt
                    | Eq => compare s1' s2'
                  end
        end
    end.
  
  (** Auxiliary functions for inserting at front and merging intervals *)
  Definition merge_interval_size (x1 : Z) (c1 : N) (x2 : Z) (c2 : N) : N :=
    (N.max c1 (Z.to_N (x2 + Z.of_N c2 - x1))).

  Fixpoint insert_interval_begin (x : Z) (c : N) (l : t) := 
    match l with
    | nil => (x,c)::nil
    | (y, c')::l' => 
         match (Z.compare (x + Z.of_N c) y) with
         | Lt => (x, c) :: l
         | Eq => (x, (c+c')%N) :: l'
         | Gt => insert_interval_begin x (merge_interval_size x c y c') l'
         end
    end.

  (** adding an element needs to be defined carefully again in order to
      generate efficient code *)
  Fixpoint addZ_aux (acc : list (Z * N)) (x : Z) (s : t) :=
    match s with
    | nil => List.rev' ((x, (1%N))::acc)
    | (y, c) :: l =>
        match (interval_1_compare x (y,c)) with
          | ICR_before       => List.rev_append ((x, (1%N))::acc) s
          | ICR_before_touch => List.rev_append ((x, N.succ c)::acc) l
          | ICR_after        => addZ_aux ((y,c) :: acc) x l
          | ICR_after_touch  => List.rev_append acc (insert_interval_begin y (N.succ c) l)
          | _  => List.rev_append ((y, c)::acc) l
        end
    end.

  Definition addZ x s := addZ_aux nil x s.
  Definition add x s := addZ (Enc.encode x) s.

  (** [add_list] is a simple extension to add many elements.
      This is used to define the function [from_elements]. *)
  Definition add_list (l : list elt) (s : t) : t :=
     List.fold_left (fun s x => add x s) l s.

  Definition from_elements (l : list elt) : t := add_list l empty.

  (** [singleton] is trivial to define *)
  Definition singleton (x : elt) : t := (Enc.encode x, 1%N) :: nil.

  Lemma singleton_alt_def : forall x, singleton x = add x empty. 
  Proof. by []. Qed.


  (** removing needs to be done with code extraction in mind again. *)
  Definition insert_intervalZ_guarded (x : Z) (c : N) s :=
     if (N.eqb c 0) then s else (x, c) :: s.

  Fixpoint removeZ_aux (acc : list (Z * N)) (x : Z) (s : t) : t :=
    match s with
    | nil => List.rev' acc
    | (y, c) :: l =>
        if (Z.ltb x y) then List.rev_append acc s else
        if (Z.ltb x (y+Z.of_N c)) then (
           List.rev_append (insert_intervalZ_guarded (Z.succ x) 
              (Z.to_N ((y+Z.of_N c)- (Z.succ x))) 
             (insert_intervalZ_guarded y (Z.to_N (x-y)) acc)) l
        ) else removeZ_aux ((y,c)::acc) x l
    end.

  Definition removeZ (x : Z) (s : t) : t := removeZ_aux nil x s.
  Definition remove (x : elt) (s : t) : t := removeZ (Enc.encode x) s.

  Definition remove_list (l : list elt) (s : t) : t :=
     List.fold_left (fun s x => remove x s) l s.

  (** union *)
  Fixpoint union_aux (s1 : t) :=
    fix aux (s2 : t) (acc : list (Z * N)) :=
    match (s1, s2) with
    | (nil, _) => List.rev_append acc s2
    | (_, nil) => List.rev_append acc s1
    | ((y1, c1) :: l1, (y2, c2) :: l2) =>
        match (interval_compare (y1, c1) (y2,c2)) with
          | ICR_before       => union_aux l1 s2 ((y1, c1)::acc)
          | ICR_before_touch => 
              union_aux l1 (
               insert_interval_begin y1 ((c1+c2)%N) l2) acc
          | ICR_after        => aux l2 ((y2, c2)::acc)
          | ICR_after_touch  => union_aux l1 (
              insert_interval_begin y2 ((c1+c2)%N) l2) acc
          | ICR_overlap_before => 
              union_aux l1 (insert_interval_begin y1 (merge_interval_size y1 c1 y2 c2) l2) acc
          | ICR_overlap_after => 
              union_aux l1 (insert_interval_begin y2 (merge_interval_size y2 c2 y1 c1) l2) acc
          | ICR_equal => union_aux l1 s2 acc
          | ICR_subsume_1 => union_aux l1 s2 acc
          | ICR_subsume_2 => aux l2 acc
        end
    end.

  Definition union s1 s2 := union_aux s1 s2 nil.

  (** diff *)


  Fixpoint diff_aux (y2 : Z) (c2 : N) (acc : list (Z * N)) (s : t) : (list (Z * N) * t) :=
    match s with
    | nil => (acc, nil)
    | ((y1, c1) :: l1) =>
        match (interval_compare (y1, c1) (y2,c2)) with
          | ICR_before       => diff_aux y2 c2 ((y1, c1)::acc) l1
          | ICR_before_touch => diff_aux y2 c2 ((y1, c1)::acc) l1
          | ICR_after        => (acc, s)
          | ICR_after_touch  => (acc, s)
          | ICR_overlap_before => diff_aux y2 c2 ((y1, Z.to_N (y2 - y1))::acc) l1
          | ICR_overlap_after => (acc, (y2+Z.of_N c2, Z.to_N ((y1 + Z.of_N c1) - (y2 + Z.of_N c2))) :: l1)
          | ICR_equal => (acc, l1)
          | ICR_subsume_1 => diff_aux y2 c2 acc l1
          | ICR_subsume_2 => ((insert_intervalZ_guarded y1
                (Z.to_N (y2 - y1)) acc), 
              insert_intervalZ_guarded (y2+Z.of_N c2) (Z.to_N ((y1 + Z.of_N c1) - (y2 + Z.of_N c2))) l1) 
        end
    end.

  Fixpoint diff_aux2 (acc : list (Z * N)) (s1 s2 : t) : (list (Z * N)) :=
    match (s1, s2) with
    | (nil, _) => rev_append acc s1
    | (_, nil) => rev_append acc s1
    | (_, (y2, c2) :: l2) =>
      match diff_aux y2 c2 acc s1 with
        (acc', s1') => diff_aux2 acc' s1' l2
      end
    end.

  Definition diff s1 s2 := diff_aux2 nil s1 s2.
  
  (** subset *)
  Fixpoint subset (s1 : t) :=
    fix aux (s2 : t) :=
    match (s1, s2) with
    | (nil, _) => true
    | (_ :: _, nil) => false
    | ((y1, c1) :: l1, (y2, c2) :: l2) =>
        match (interval_compare (y1, c1) (y2,c2)) with
          | ICR_before       => false
          | ICR_before_touch => false
          | ICR_after        => aux l2 
          | ICR_after_touch  => false
          | ICR_overlap_before => false
          | ICR_overlap_after => false
          | ICR_equal => subset l1 l2
          | ICR_subsume_1 => subset l1 s2
          | ICR_subsume_2 => false
        end
    end.

  (** equal *)
  Fixpoint equal (s s' : t) : bool := match s, s' with
    | nil, nil => true
    | ((x,cx)::xs), ((y,cy)::ys) => andb (Z.eqb x y) (andb (N.eqb cx cy) (equal xs ys))
    | _, _ => false
  end. 

  (** inter *)
  Fixpoint inter_aux (y2 : Z) (c2 : N) (acc : list (Z * N)) (s : t) : (list (Z * N) * t) :=
    match s with
    | nil => (acc, nil)
    | ((y1, c1) :: l1) =>
        match (interval_compare (y1, c1) (y2,c2)) with
          | ICR_before       => inter_aux y2 c2 acc l1
          | ICR_before_touch => inter_aux y2 c2 acc l1
          | ICR_after        => (acc, s)
          | ICR_after_touch  => (acc, s)
          | ICR_overlap_before => inter_aux y2 c2 ((y2, Z.to_N (y1 + Z.of_N c1 - y2))::acc) l1
          | ICR_overlap_after => ((y1, Z.to_N (y2 + Z.of_N c2 - y1))::acc, s)
          | ICR_equal => ((y1,c1)::acc, l1)
          | ICR_subsume_1 => inter_aux y2 c2 ((y1, c1)::acc) l1
          | ICR_subsume_2 => ((y2, c2)::acc, s)
        end
    end.

  Fixpoint inter_aux2 (acc : list (Z * N)) (s1 s2 : t) : (list (Z * N)) :=
    match (s1, s2) with
    | (nil, _) => List.rev' acc
    | (_, nil) => List.rev' acc
    | (_, (y2, c2) :: l2) =>
      match inter_aux y2 c2 acc s1 with
        (acc', s1') => inter_aux2 acc' s1' l2
      end
    end.

  Definition inter s1 s2 := inter_aux2 nil s1 s2.


  (** Partition and filter *)

  Definition partitionZ_fold_insert
             (cur : option (Z * N)) (x : Z) :=
    match cur with
       None => (x, 1%N)
     | Some (y, c) => (y, N.succ c)
    end.

  Definition partitionZ_fold_skip (acc : list (Z * N))
             (cur : option (Z * N)) : (list (Z * N)) :=
    match cur with
       None => acc
     | Some yc => yc::acc
    end.
  
  Definition partitionZ_fold_fun f st (x : Z) :=
    match st with ((acc_t, c_t), (acc_f, c_f)) =>
      if (f x) then
        ((acc_t, Some (partitionZ_fold_insert c_t x)),
         (partitionZ_fold_skip acc_f c_f, None))
      else
        ((partitionZ_fold_skip acc_t c_t, None),
         (acc_f, Some (partitionZ_fold_insert c_f x)))
    end.
  
  Definition partitionZ_single_aux f st (x : Z) (c : N) :=
    snd (fold_elementsZ_single (fun st x => Some (partitionZ_fold_fun f st x)) st x c).

  Definition partitionZ_single f acc_t acc_f x c :=
    match partitionZ_single_aux f ((acc_t, None), (acc_f, None)) x c with
    | ((acc_t, c_t), (acc_f, c_f)) =>
        (partitionZ_fold_skip acc_t c_t,
         partitionZ_fold_skip acc_f c_f)
    end.

  Fixpoint partitionZ_aux acc_t acc_f f s :=
    match s with
    | nil => (List.rev acc_t, List.rev acc_f)
    | (y, c) :: s' =>
      match partitionZ_single f acc_t acc_f y c with
      | (acc_t', acc_f') => partitionZ_aux acc_t' acc_f' f s'
      end
    end.

  Definition partitionZ := partitionZ_aux nil nil.

  Definition partition (f : elt -> bool) : t -> (t * t) :=
    partitionZ (fun z => f (Enc.decode z)).


  Definition filterZ_fold_fun f st (x : Z) :=
    match st with (acc_t, c_t) =>
      if (f x) then
        (acc_t, Some (partitionZ_fold_insert c_t x))
      else
        (partitionZ_fold_skip acc_t c_t, None)
    end.
  
  Definition filterZ_single_aux f st (x : Z) (c : N) :=
    snd (fold_elementsZ_single (fun st x => Some (filterZ_fold_fun f st x)) st x c).

  Definition filterZ_single f acc x c :=
    match filterZ_single_aux f (acc, None) x c with
    | (acc, c) =>
        (partitionZ_fold_skip acc c)
    end.

  Fixpoint filterZ_aux acc f s :=
    match s with
    | nil => (List.rev acc)
    | (y, c) :: s' =>
      filterZ_aux (filterZ_single f acc y c) f s'
    end.
  
  Definition filterZ := filterZ_aux nil.

  Definition filter (f : elt -> bool) : t -> t :=
    filterZ (fun z => f (Enc.decode z)).

  
  (** Simple wrappers *)

  Definition fold {B : Type} (f : elt -> B -> B) (s : t) (i : B) : B :=
    snd (fold_elementsZ (fun b z => Some (f (Enc.decode z) b)) i s).

  Definition for_all (f : elt -> bool) (s : t) : bool :=
    snd (fold_elementsZ (fun b z =>
      if b then
        Some (f (Enc.decode z))
      else None) true s).

  Definition exists_ (f : elt -> bool) (s : t) : bool :=
    snd (fold_elementsZ (fun b z =>
      if b then
        None
      else Some (f (Enc.decode z))) false s).

  Fixpoint cardinalN c (s : t) : N := match s with
    | nil => c
    | (_,cx)::xs => cardinalN (c + cx)%N xs
  end. 

  Definition cardinal (s : t) : nat := N.to_nat (cardinalN (0%N) s).

  Definition min_eltZ (s : t) : option Z :=
    match s with
    | nil => None
    | (x, _) :: _ => Some x
    end.

  Definition min_elt (s : t) : option elt :=
    match (min_eltZ s) with
    | None => None
    | Some x => Some (Enc.decode x)
    end.

  Definition choose := min_elt.

  Fixpoint max_eltZ (s : t) : option Z :=
    match s with
    | nil => None
    | (x, c) :: nil => Some (Z.pred (x + Z.of_N c))
    | (x, _) :: s' => max_eltZ s'
    end.

  Definition max_elt (s : t) : option elt :=
    match (max_eltZ s) with
    | None => None
    | Some x => Some (Enc.decode x)
    end.
  
End Ops.


(** ** Raw Module 
   
    Following the idea of [MSetInterface.RawSets], we first
    define a module [Raw] proves all the required properties with
    respect to an explicitly provided invariant. In a next step, this
    invariant is then moved into the set type. This allows to instantiate
    the [WSetsOn] interface. *)
Module Raw (Enc : ElementEncode).
  Include (Ops Enc).

  (** *** Defining invariant [IsOk] *)
  Definition is_encoded_elems_list (l : list Z) : Prop :=
    (forall x, List.In x l -> exists e, Enc.encode e = x).

  Definition interval_list_elements_greater (x : Z) (l : t) : bool :=
    match l with 
      | nil => true
      | (y, _)::_ => Z.ltb x y 
    end.

  Fixpoint interval_list_invariant (l : t) :=
   match l with
   | nil => true
   | (x, c) :: l' => 
       interval_list_elements_greater (x + (Z.of_N c)) l' && negb (N.eqb c 0) && interval_list_invariant l'
   end.

  Definition IsOk s := (interval_list_invariant s = true /\ is_encoded_elems_list (elementsZ s)).


  (** *** Defining notations *)
  Section ForNotations.

    Class Ok (s:t) : Prop := ok : IsOk s.
    Hint Resolve @ok.
    Hint Unfold Ok.
    Instance IsOk_Ok s `(Hs : IsOk s) : Ok s := { ok := Hs }.

    Definition In x s := (SetoidList.InA Enc.E.eq x (elements s)).
    Definition InZ x s := (List.In x (elementsZ s)).
    Definition Equal s s' := forall a : elt, In a s <-> In a s'.
    Definition Subset s s' := forall a : elt, In a s -> In a s'.
    Definition Empty s := forall a : elt, ~ In a s.
    Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
    Definition Exists (P : elt -> Prop) (s : t) := exists x, In x s /\ P x.

  End ForNotations.

  (** *** elements list properties
  
      The functions [elementsZ], [elementsZ_single], 
      [elements] and [elements_single] are crucial and used
      everywhere. Therefore, we first establish a few properties of
      these important functions. *)
                    
  Lemma elementsZ_nil : (elementsZ (nil : t) = nil). 
  Proof. done. Qed.

  Lemma elements_nil : (elements (nil : t) = nil). 
  Proof. done. Qed.

  Definition elementsZ_single (x:Z) (c:N) := 
      List.rev' (N.peano_rec (fun _ => list Z)
                  nil (fun n ls => (x+Z.of_N n)%Z :: ls) c).

  Definition elements_single x c :=
    List.map Enc.decode (elementsZ_single x c).

  Lemma elementsZ_single_base : forall x,
    elementsZ_single x (0%N) = nil.
  Proof. done. Qed.

  Lemma elementsZ_single_succ : forall x c,
    elementsZ_single x (N.succ c) = 
    elementsZ_single x c ++ (x+Z.of_N c)::nil.
  Proof. 
    intros x c.
    rewrite /elementsZ_single N.peano_rec_succ /rev' -!rev_alt //.
  Qed.

  Lemma elementsZ_single_add : forall x c2 c1,
    elementsZ_single x (c1 + c2)%N = 
    elementsZ_single x c1 ++ elementsZ_single (x+Z.of_N c1) c2.
  Proof. 
    intros x.
    induction c2 as [| c2' IH] using N.peano_ind. {
      move => c1.
      rewrite elementsZ_single_base /= app_nil_r N.add_0_r //.
    } {
      move => c1.
      rewrite N.add_succ_r !elementsZ_single_succ IH app_assoc N2Z.inj_add Z.add_assoc //.
    }
  Qed.

  Lemma elementsZ_single_succ_front : forall x c,
    elementsZ_single x (N.succ c) = 
    x :: elementsZ_single (Z.succ x) c.
  Proof. 
    intros x c.
    rewrite -N.add_1_l elementsZ_single_add.
    rewrite N.one_succ elementsZ_single_succ elementsZ_single_base /= Z.add_0_r.
    by rewrite Z.add_1_r.
  Qed.

  Lemma In_elementsZ_single : forall c y x,
    List.In y (elementsZ_single x c) <->
    (x <= y) /\ (y < (x+Z.of_N c)).
  Proof.
    induction c as [| c' IH] using N.peano_ind. {
      intros y x.
      rewrite elementsZ_single_base Z.add_0_r /=.
      omega.
    } {
      intros y x.
      rewrite elementsZ_single_succ in_app_iff IH /= N2Z.inj_succ Z.add_succ_r Z.lt_succ_r.
      split. {
        move => [ | []] //. { 
          move => [H_x_le H_y_le]. 
          omega.
        } {
          move => <-.
          split.
            - by apply Z_le_add_r.
            - by apply Z.le_refl.
        }
      } {
        move => [H_x_le] H_y_lt.
        omega.
      }
    }
  Qed.

  Lemma In_elementsZ_single1 : forall y x,
    List.In y (elementsZ_single x (1%N)) <->
    (x = y).
  Proof.
    intros y x.
    rewrite In_elementsZ_single /= Z.add_1_r Z.lt_succ_r. 
    omega.
  Qed.

  Lemma length_elementsZ_single : forall cx x,
    length (elementsZ_single x cx) = N.to_nat cx.
  Proof.
    induction cx as [| cx' IH] using N.peano_ind. {
      by simpl.
    } {
      intros x.
      rewrite elementsZ_single_succ_front /=.
      rewrite IH N2Nat.inj_succ //.
    }
  Qed.

  Lemma fold_elementsZ_aux_irrel {A} :
    forall f c (acc : A) x H1 H2,
      fold_elementsZ_aux f acc x c H1 =
      fold_elementsZ_aux f acc x c H2.
  Proof.
    intros f c.
    induction c as [c IH] using (well_founded_ind lt_wf_0).
    case_eq c. {
      intros H_c acc x; case; intro H_H1; case; intro H_H2.
      reflexivity.
    } {
      intros p H_c acc x; case; intro H_H1; case; intro H_H2.
      unfold fold_elementsZ_aux; fold (@fold_elementsZ_aux A).
      case (f acc x) => // acc'.
      apply IH.
      rewrite H_c.
      apply N.lt_pred_l.
      discriminate.
    }
  Qed.


  Lemma fold_elementsZ_single_pos {A} : forall f (acc : A) x p,
    fold_elementsZ_single f acc x (N.pos p) =
    match f acc x with
    | Some acc' =>
        fold_elementsZ_single f acc' (Z.succ x)
         (N.pred (N.pos p))
    | None => (true, acc)
    end.
  Proof.
    intros f acc x p.        
    unfold fold_elementsZ_single.
    unfold fold_elementsZ_aux.
    case: (lt_wf_0 _).
    fold (@fold_elementsZ_aux A).
    intro.
    case (f acc x) => // acc'.
    apply fold_elementsZ_aux_irrel.
  Qed.


  Lemma fold_elementsZ_single_zero {A} : forall f (acc : A) x,
      fold_elementsZ_single f acc x (0%N) = (false, acc).
  Proof.
    intros f acc x.
    unfold fold_elementsZ_single.
    case (lt_wf_0 (0%N)); intro.
    unfold fold_elementsZ_aux.
    reflexivity.
  Qed.


  Lemma fold_elementsZ_single_succ {A} : forall f (acc : A) x c,
    fold_elementsZ_single f acc x (N.succ c) =
    match f acc x with
      | Some acc' =>
          fold_elementsZ_single f acc' (Z.succ x) c
      | None => (true, acc)
    end.
  Proof.
    intros f acc x c.
    case c. {
      by rewrite fold_elementsZ_single_pos.
    } {
      intro p; simpl.
      rewrite fold_elementsZ_single_pos.
      case (f acc x) => // acc' /=.
      by rewrite Pos.pred_N_succ.
    }
  Qed.

  Fixpoint fold_opt {A B} f (acc : A) (bs : list B) : (bool * A) :=
    match bs with
      | nil => (false, acc)
      | (b :: bs') =>
        match f acc b with
        | Some acc' => fold_opt f acc' bs'
        | None => (true, acc)
        end
    end.

  Lemma fold_opt_list_cons : forall {A} (bs : list A) (acc : list A),
    fold_opt (fun l x => Some (x :: l)) acc bs =
    (false, List.rev bs ++ acc).
  Proof.
    induction bs as [| b bs' IH] => acc. {
      by simpl.
    } {
      rewrite /= IH -app_assoc //.
    }
  Qed.

  Lemma fold_opt_app {A B} : forall f (acc : A) (l1 l2 : list B),
    fold_opt f acc (l1 ++ l2) =
    (let (ab, acc') := fold_opt f acc l1 in
     if ab then (true, acc') else fold_opt f acc' l2).
  Proof.
    intros f acc l1 l2.
    move : acc.
    induction l1 as [| b l1' IH] => acc. {
      rewrite app_nil_l //.
    } {
      rewrite /=.
      case (f acc b); last done.
      intro acc'.
      rewrite IH //.
    }
  Qed.

  
  Lemma fold_elementsZ_single_alt_def {A} : forall f c (acc : A) x,
     fold_elementsZ_single f acc x c =
     fold_opt f acc (elementsZ_single x c).
  Proof.
    intro f.
    induction c as [| c' IH] using N.peano_ind. {
      intros acc x.
      rewrite fold_elementsZ_single_zero
              elementsZ_single_base /fold_opt //.
    } {
      intros acc x.
      rewrite fold_elementsZ_single_succ
              elementsZ_single_succ_front /=.
      case (f acc x); last reflexivity.
      intro acc'.
      apply IH.
    }
  Qed.

  Lemma fold_elementsZ_nil {A} : forall f (acc : A),
     fold_elementsZ f acc nil = (false, acc).
  Proof. done. Qed.

  Lemma fold_elementsZ_cons {A} : forall f (acc : A) y c s,
    fold_elementsZ f acc ((y, c)::s) =
    (let (ab, acc') := fold_elementsZ_single f acc y c in
     if ab then (true, acc') else fold_elementsZ f acc' s).
  Proof.
    intros f acc y c s.
    done.
  Qed.


  Lemma fold_elementsZ_alt_def_aux : forall (s : t) base,
    (snd (fold_elementsZ
      (fun (l : list Z) (x : Z) => Some (x :: l)) base s)) =
    elementsZ s ++ base.
  Proof.
    induction s as [| [y1 c1] s' IH] => base. {
      rewrite elementsZ_nil /fold_elementsZ /fold_opt /snd
        app_nil_l //.
    } {
      rewrite /elementsZ !fold_elementsZ_cons.
      rewrite !fold_elementsZ_single_alt_def !fold_opt_list_cons.
      rewrite !IH app_nil_r app_assoc //.
    }
  Qed.

  
  Lemma fold_elementsZ_alt_def {A} : forall f s (acc : A),
     fold_elementsZ f acc s =
     fold_opt f acc (rev (elementsZ s)).
  Proof.
    intro f.
    induction s as [| [y1 c1] s' IH] => acc. {
      by simpl.
    } {
      rewrite /elementsZ !fold_elementsZ_cons.
      rewrite !fold_elementsZ_single_alt_def
              fold_opt_list_cons app_nil_r
              fold_elementsZ_alt_def_aux rev_app_distr
              rev_involutive fold_opt_app.
      case (fold_opt f acc (elementsZ_single y1 c1)).
      move => [] //.
    }
  Qed.

  Lemma elementsZ_cons : forall x c s, elementsZ (((x, c) :: s) : t) = 
     ((elementsZ s) ++ (List.rev (elementsZ_single x c))). 
  Proof. 
    intros x c s.
    rewrite /elementsZ fold_elementsZ_cons
            !fold_elementsZ_alt_def 
            fold_elementsZ_single_alt_def.
    rewrite !fold_opt_list_cons.
    rewrite !app_nil_r !rev_involutive /=.
    rewrite fold_elementsZ_alt_def_aux //.
  Qed.

  Lemma elements_cons : forall x c s, elements (((x, c) :: s) : t) = 
     ((elements_single x c) ++ elements s). 
  Proof. 
    intros x c s.
    rewrite /elements /elements_single elementsZ_cons.
    rewrite !rev_map_alt_def map_app rev_app_distr map_rev rev_involutive //. 
  Qed.

  Lemma elementsZ_app : forall (s1 s2 : t), elementsZ (s1 ++ s2) = 
     ((elementsZ s2) ++ (elementsZ s1)). 
  Proof. 
    induction s1 as [| [x1 c1] s1 IH1]. {
      move => s2.
      rewrite elementsZ_nil app_nil_r //.
    } 
    move => s2.
    rewrite -app_comm_cons !elementsZ_cons IH1 -app_assoc //.
  Qed.

  Lemma InZ_nil : forall y, InZ y nil <-> False. 
  Proof. 
    intro y.
    done.
  Qed.

  Lemma InZ_cons : forall y x c s, InZ y (((x, c) :: s) : t) <-> 
     List.In y (elementsZ_single x c) \/ InZ y s. 
  Proof. 
    intros y x c s.
    rewrite /InZ elementsZ_cons in_app_iff -in_rev.
    firstorder.
  Qed.

  Lemma InZ_app : forall s1 s2 y, 
     InZ y (s1 ++ s2) <-> InZ y s1 \/ InZ y s2.
  Proof. 
    intros s1 s2 y.   
    rewrite /InZ elementsZ_app in_app_iff.
    tauto.
  Qed.

  Lemma InZ_rev : forall s y, 
     InZ y (List.rev s) <-> InZ y s.
  Proof. 
    intros s x.
    rewrite /InZ.
    induction s as [| [y c] s' IH]; first done.
    simpl.
    rewrite elementsZ_app in_app_iff IH.
    rewrite !elementsZ_cons !in_app_iff elementsZ_nil
            -!in_rev /=.
    tauto.
  Qed.

  Lemma In_elementsZ_single_dec : forall y x c,
    {List.In y (elementsZ_single x c)} +
    {~ List.In y (elementsZ_single x c)}.
  Proof.  
    intros y x c.
    case (Z_le_dec x y); last first. {
      right; rewrite In_elementsZ_single; tauto.
    }
    case (Z_lt_dec y (x + Z.of_N c)); last first. {
      right; rewrite In_elementsZ_single; tauto.
    }
    left; rewrite In_elementsZ_single; tauto.
  Qed.

  Lemma InZ_dec : forall y s, 
     {InZ y s} + {~InZ y s}.
  Proof. 
    intros y.
    induction s as [| [x c] s IH]. {
      by right.
    }
    move : IH => [] IH. {
      by left; rewrite InZ_cons; right.
    }
    case (In_elementsZ_single_dec y x c). {
      by left; rewrite InZ_cons; left.
    } {
      by right; rewrite InZ_cons; tauto.
    }
  Qed.

  Lemma In_elementsZ_single_hd : forall (c : N) x, (c <> 0)%N -> List.In x (elementsZ_single x c).
  Proof.
    intros c x H_c_neq.
    rewrite In_elementsZ_single.
    split. {
      apply Z.le_refl.
    } {
      apply Z.lt_add_pos_r.
      have -> : 0 = Z.of_N (0%N)  by [].
      apply N2Z.inj_lt.
      by apply N.neq_0_lt_0.
    }
  Qed.

 
  (** *** comparing intervals *)

  Ltac Z_named_compare_cases H := match goal with
    | [ |- context [Z.compare ?z1 ?z2] ] =>
      case_eq (Z.compare z1 z2); [move => /Z.compare_eq_iff | move => /Z.compare_lt_iff | move => /Z.compare_gt_iff]; move => H //
  end.

  Ltac Z_compare_cases := let H := fresh "H" in Z_named_compare_cases H.
  
  Lemma interval_compare_elim : forall (y1 : Z) (c1 : N) (y2 : Z) (c2 : N), 
    match (interval_compare (y1, c1) (y2, c2)) with
      | ICR_before         => (y1 + Z.of_N c1) < y2
      | ICR_before_touch   => (y1 + Z.of_N c1) = y2
      | ICR_after          => (y2 + Z.of_N c2) < y1
      | ICR_after_touch    => (y2 + Z.of_N c2) = y1
      | ICR_equal          => (y1 = y2) /\ (c1 = c2)
      | ICR_overlap_before => (y1 < y2) /\ (y2 < y1 + Z.of_N c1) /\ (y1 + Z.of_N c1 < y2 + Z.of_N c2)
      | ICR_overlap_after  => (y2 < y1) /\ (y1 < y2 + Z.of_N c2) /\ (y2 + Z.of_N c2 < y1 + Z.of_N c1)
      | ICR_subsume_1      => (y2 <= y1) /\ (y1 + Z.of_N c1 <= y2 + Z.of_N c2) /\ (y2 < y1 \/ y1 + Z.of_N c1 < y2 + Z.of_N c2)
      | ICR_subsume_2      => (y1 <= y2) /\ (y2 + Z.of_N c2 <= y1 + Z.of_N c1) /\ (y1 < y2 \/ y2 + Z.of_N c2 < y1 + Z.of_N c1)
    end.
  Proof.
    intros y1 c1 y2 c2.
    rewrite /interval_compare.
    (repeat Z_compare_cases); subst; repeat split;
       try (by apply Z.eq_le_incl); 
       try (by apply Z.lt_le_incl);
       try (by left); try (by right).

    apply Z.add_reg_l in H2.
    by apply N2Z.inj.
  Qed.

  Lemma interval_compare_swap : forall (y1 : Z) (c1 : N) (y2 : Z) (c2 : N),
    (c1 <> 0%N) \/ (c2 <> 0%N) -> 
    interval_compare (y2, c2) (y1, c1) =
    match (interval_compare (y1, c1) (y2, c2)) with
      | ICR_before         => ICR_after
      | ICR_before_touch   => ICR_after_touch
      | ICR_after          => ICR_before
      | ICR_after_touch    => ICR_before_touch
      | ICR_equal          => ICR_equal
      | ICR_overlap_before => ICR_overlap_after
      | ICR_overlap_after  => ICR_overlap_before
      | ICR_subsume_1      => ICR_subsume_2
      | ICR_subsume_2      => ICR_subsume_1
    end.
  Proof.
    intros y1 c1 y2 c2 H_c12_neq_0.
    rewrite /interval_compare.
    move : (Z.compare_antisym y1 y2) => ->.
    move : (Z.compare_antisym (y1 + Z.of_N c1) (y2 + Z.of_N c2)) => ->.
    have H_suff : y1 + Z.of_N c1 <= y2 -> y2 + Z.of_N c2 <= y1 -> False. {
      move => H1 H2.
      case H_c12_neq_0 => H_c_neq_0. {
        suff : (y1 + Z.of_N c1 <= y1). {
          apply Z.nle_gt.
          by apply Z_lt_add_r.
        }
        eapply Z.le_trans; eauto.
        eapply Z.le_trans; eauto.
        apply Z_le_add_r.
      } {
        suff : (y2 + Z.of_N c2 <= y2). {
          apply Z.nle_gt.
          by apply Z_lt_add_r.
        }
        eapply Z.le_trans; eauto.
        eapply Z.le_trans; eauto.
        apply Z_le_add_r.
      }
    }
    repeat Z_compare_cases. {
      exfalso; apply H_suff.
        - by rewrite H; apply Z.le_refl.
        - by rewrite H0; apply Z.le_refl.
    } {
      exfalso; apply H_suff.
        - by rewrite H; apply Z.le_refl.
        - by apply Z.lt_le_incl.
    } {
      exfalso; apply H_suff.
        - by apply Z.lt_le_incl.
        - by rewrite H0; apply Z.le_refl.
    } {
      exfalso; apply H_suff.
        - by apply Z.lt_le_incl.
        - by apply Z.lt_le_incl.
    }
  Qed.
  
  Lemma interval_1_compare_alt_def : forall (y : Z) (i : (Z * N)), 
    interval_1_compare y i = match (interval_compare (y, (1%N)) i) with
      | ICR_equal => ICR_subsume_1
      | ICR_subsume_1 => ICR_subsume_1
      | ICR_subsume_2 => ICR_subsume_1
      | r => r
    end.
  Proof.
    move => y1 [y2 c2].
    rewrite /interval_1_compare /interval_compare.
    replace (y1 + Z.of_N 1) with (Z.succ y1); last done.
    repeat Z_compare_cases. {
      contradict H1.
      by apply Zle_not_lt, Zlt_succ_le.
    } {
      contradict H.
      by apply Zle_not_lt, Zlt_succ_le.
    }
  Qed.

  Lemma interval_1_compare_elim : forall (y1 : Z) (y2 : Z) (c2 : N), 
    match (interval_1_compare y1 (y2, c2)) with
      | ICR_before         => Z.succ y1 < y2
      | ICR_before_touch   => y2 = Z.succ y1 
      | ICR_after          => (y2 + Z.of_N c2) < y1
      | ICR_after_touch    => (y2 + Z.of_N c2) = y1
      | ICR_equal          => False
      | ICR_overlap_before => False
      | ICR_overlap_after  => False
      | ICR_subsume_1      => (c2 = 0%N) \/ ((y2 <= y1) /\ (y1 < y2 + Z.of_N c2))
      | ICR_subsume_2      => False
    end.
  Proof.
    intros y1 y2 c2.
    move : (interval_compare_elim y1 (1%N) y2 c2).
    rewrite interval_1_compare_alt_def.
    have H_succ: forall z, z + Z.of_N 1 = Z.succ z by done.

    case_eq (interval_compare (y1, 1%N) (y2, c2)) => H_comp;
      rewrite ?H_succ ?Z.lt_succ_r ?Z.le_succ_l //. {
      move => [H_lt] [H_le] _.
      contradict H_lt.
      by apply Zle_not_lt.
    } {
      move => [_] [H_lt] H_le.
      contradict H_lt.
      by apply Zle_not_lt.
    } {
      move => [->] <-.
      rewrite ?Z.lt_succ_r.
      right.
      split; apply Z.le_refl.
    } {
      tauto.
    } {
      case (N.zero_or_succ c2). { 
        move => -> _; by left.
      } {
        move => [c2'] ->.
        rewrite !N2Z.inj_succ Z.add_succ_r -Z.succ_le_mono Z.le_succ_l.
        move => [H_y1_le] [H_le_y1].        
        suff -> : y1 = y2. {
          move => [] H_pre; contradict H_pre. {
            apply Z.lt_irrefl.
          } {
            apply Zle_not_lt, Z_le_add_r.
          }
        }
        apply Z.le_antisymm => //.
        eapply Z.le_trans; last apply H_le_y1.
        apply Z_le_add_r.
      }
    }
  Qed.
      
   (** *** Alternative definition of addZ *)
  Lemma addZ_aux_alt_def : forall x s acc,
    addZ_aux acc x s = (List.rev acc) ++ addZ x s. 
  Proof. 
    intros y1 s.
    unfold addZ.
    induction s as [| [y2 c2] s' IH] => acc. {
      rewrite /addZ_aux /addZ /= /rev' !rev_append_rev /= app_nil_r //.
    } {
      unfold addZ_aux.
      case (interval_1_compare y1 (y2, c2)); fold addZ_aux;
        rewrite ?rev_append_rev /= ?app_assoc_reverse //.
      rewrite (IH ((y2,c2)::acc)) (IH ((y2,c2)::nil)).
      rewrite /= app_assoc_reverse //.
    }
  Qed.
       
  Lemma addZ_alt_def : forall x s, 
    addZ x s =
    match s with
    | nil => (x, (1%N))::nil
    | (y, c) :: l =>
        match (interval_1_compare x (y,c)) with
          | ICR_before       => (x, (1%N))::s
          | ICR_before_touch => (x, N.succ c)::l
          | ICR_after        => (y,c)::(addZ x l)
          | ICR_after_touch  => insert_interval_begin y (N.succ c) l
          | _  => (y, c)::l
        end
    end.
  Proof.
    intros x s.
    rewrite /addZ.
    case s => //.
    move => [y c] s'.
    unfold addZ_aux.
    case (interval_1_compare x (y, c)); fold addZ_aux;
      rewrite ?rev_append_rev /= ?app_assoc_reverse //.
    rewrite addZ_aux_alt_def //.
  Qed.
   

    
  (** *** Auxiliary Lemmata about Invariant *)

  Lemma interval_list_elements_greater_cons : forall z x c s,
    interval_list_elements_greater z ((x, c) :: s) = true <-> 
    (z < x).  
  Proof.
    intros z x c s.
    rewrite /=.
    apply Z.ltb_lt.
  Qed.

  Lemma interval_list_elements_greater_impl : forall x y s,
    (y <= x) -> 
    interval_list_elements_greater x s = true -> 
    interval_list_elements_greater y s = true.
  Proof.
    intros x y s.
    case s => //.
    move => [z c] s'.
    rewrite /interval_list_elements_greater.
    move => H_y_leq /Z.ltb_lt H_x_lt.
    apply Z.ltb_lt.
    eapply Z.le_lt_trans; eauto.
  Qed.

  Lemma interval_list_invariant_nil : interval_list_invariant nil = true.
  Proof.
    by [].
  Qed.
 
  Lemma Ok_nil : Ok nil <-> True. 
  Proof.
    rewrite /Ok /IsOk /interval_list_invariant /is_encoded_elems_list //.
  Qed.

  Lemma is_encoded_elems_list_app : forall l1 l2,
    is_encoded_elems_list (l1 ++ l2) <->
    (is_encoded_elems_list l1 /\ is_encoded_elems_list l2).
  Proof.
    intros l1 l2.
    rewrite /is_encoded_elems_list.
    setoid_rewrite in_app_iff.
    split; firstorder.
  Qed.

  Lemma is_encoded_elems_list_rev : forall l,
    is_encoded_elems_list (List.rev l) <->
    is_encoded_elems_list l.
  Proof.
    intros l.
    rewrite /is_encoded_elems_list.
    split; (
      move => H x H_in;
      apply H;
      move : H_in;
      rewrite -in_rev => //
    ).
  Qed.

  Lemma interval_list_invariant_cons : forall y c s', 
    interval_list_invariant ((y, c) :: s') = true <-> 
    (interval_list_elements_greater (y+Z.of_N c) s' = true /\ 
      ((c <> 0)%N) /\ interval_list_invariant s' = true). 
  Proof.
    rewrite /interval_list_invariant -/interval_list_invariant.
    intros y c s'.
    rewrite !Bool.andb_true_iff negb_true_iff.
    split. {
      move => [] [H_inf] /N.eqb_neq H_c H_s'. tauto.
    } {                           
      move => [H_inf] [/N.eqb_neq H_c] H_s'. tauto.
    }
  Qed.

  Lemma interval_list_invariant_sing : forall x c,
    interval_list_invariant ((x, c)::nil) = true <-> (c <> 0)%N.
  Proof.
    intros x c.
    rewrite interval_list_invariant_cons.
    split; tauto.
  Qed.

  Lemma Ok_cons : forall y c s', Ok ((y, c) :: s') <-> 
    (interval_list_elements_greater (y+Z.of_N c) s' = true /\ ((c <> 0)%N) /\ 
     is_encoded_elems_list (elementsZ_single y c) /\ Ok s'). 
  Proof.
    intros y c s'.
    rewrite /Ok /IsOk interval_list_invariant_cons elementsZ_cons is_encoded_elems_list_app
       is_encoded_elems_list_rev.
    tauto.
  Qed.

  Lemma Nin_elements_greater : forall s y,
     interval_list_elements_greater y s = true ->
     interval_list_invariant s = true ->
     forall x, x <= y -> ~(InZ x s).
  Proof.
    induction s as [| [z c] s' IH]. {
      intros y _ _ x _.
      by simpl.
    } {
      move => y /interval_list_elements_greater_cons H_y_lt
        /interval_list_invariant_cons [H_gr] [H_c] H_s'
        x H_x_le.
      rewrite InZ_cons In_elementsZ_single. 
      have H_x_lt : x < z by eapply Z.le_lt_trans; eauto.

      move => []. {              
        move => [H_z_leq] _; contradict H_z_leq.
        by apply Z.nle_gt.
      } {
        eapply IH; eauto.
        by apply Z_lt_le_add_r.
      }
    }
  Qed.

  Lemma Nin_elements_greater_equal :
     forall x s,
       interval_list_elements_greater x s = true ->
       interval_list_invariant s = true ->
       ~ (InZ x s). 
  Proof.
    move => x s H_inv H_gr. 
    apply (Nin_elements_greater s x) => //.
    apply Z.le_refl.
  Qed.

  Lemma interval_list_elements_greater_alt_def : forall s y,
     interval_list_invariant s = true ->

     (interval_list_elements_greater y s = true <->
      (forall x, x <= y -> ~(InZ x s))).
  Proof.
    intros s y H_inv.
    split. {
      move => H_gr.
      apply Nin_elements_greater => //.
    } {
      move : H_inv.
      case s as [| [x2 c] s'] => //.
      rewrite interval_list_invariant_cons interval_list_elements_greater_cons.
      move => [_] [H_c_neq] _ H.
      apply Z.nle_gt => H_ge.
      apply (H x2) => //.
      rewrite InZ_cons; left.
      apply In_elementsZ_single_hd => //.
    }
  Qed.

  Lemma interval_list_elements_greater_alt2_def : forall s y,
     interval_list_invariant s = true ->

     (interval_list_elements_greater y s = true <->
      (forall x, InZ x s -> y < x)).
  Proof.
    intros s y H.
    rewrite interval_list_elements_greater_alt_def //.
    firstorder.
    apply Z.nle_gt.
    move => H_lt.
    eapply H0; eauto.
  Qed.

  Lemma interval_list_elements_greater_intro : forall s y,
     interval_list_invariant s = true ->
     (forall x, InZ x s -> y < x) ->
     interval_list_elements_greater y s = true.
  Proof.
    intros s y H1 H2.
    rewrite interval_list_elements_greater_alt2_def //.
  Qed.
               
  Lemma interval_list_elements_greater_app_elim_1 : forall s1 s2 y,
    interval_list_elements_greater y (s1 ++ s2) = true ->
    interval_list_elements_greater y s1 = true.
  Proof.
    intros s1 s2 y.
    case s1 => //.
  Qed.

  Lemma interval_list_invariant_app_intro : forall s1 s2,
      interval_list_invariant s1 = true ->
      interval_list_invariant s2 = true ->
      (forall (x1 x2 : Z), InZ x1 s1 -> InZ x2 s2 -> Z.succ x1 < x2) ->
      interval_list_invariant (s1 ++ s2) = true.
  Proof.
    induction s1 as [| [y1 c1] s1' IH]. {
      move => s2 _ //.
    } {
      move => s2.
      rewrite -app_comm_cons !interval_list_invariant_cons.
      move => [H_gr] [H_c1_neq] H_inv_s1' H_inv_s2 H_inz_s2.
      split; last split. {
        move : H_gr H_inz_s2.
        case s1' as [| [y1' c1'] s1'']; last done.
        move => _ H_inz_s2.
        rewrite app_nil_l.
        apply interval_list_elements_greater_intro => //.
        move => x H_x_in_s2.
        suff H_inz : InZ (Z.pred (y1 + Z.of_N c1)) ((y1, c1) :: nil). {
          move : (H_inz_s2 _ _ H_inz H_x_in_s2).
          by rewrite Z.succ_pred.
        }
        rewrite InZ_cons In_elementsZ_single -Z.lt_le_pred; left.
        split. {
          by apply Z_lt_add_r.
        } {
          apply Z.lt_pred_l.
        }
      } {
        assumption.
      } {
        apply IH => //.
        intros x1 x2 H_in_x1 H_in_x2.
        apply H_inz_s2 => //.
        rewrite InZ_cons; by right.
      }
    }
  Qed.


  Lemma interval_list_invariant_app_elim : forall s1 s2,
      interval_list_invariant (s1 ++ s2) = true ->
      interval_list_invariant s1 = true /\
      interval_list_invariant s2 = true /\
      (forall (x1 x2 : Z), InZ x1 s1 -> InZ x2 s2 -> Z.succ x1 < x2).
  Proof.
    move => s1 s2.
    induction s1 as [| [y1 c1] s1' IH]; first done.
    rewrite -app_comm_cons !interval_list_invariant_cons.

    move => [H_gr] [H_c1_neq_0] /IH [H_inv_s1'] [H_inv_s2] H_in_s1'_s2.
    repeat split; try assumption. {
      move : H_gr.
      case s1'; first done.
      move => [y2 c2] s1''.
      rewrite interval_list_elements_greater_cons //.
    } {
      move => x1 x2.
      rewrite InZ_cons In_elementsZ_single.
      move => []; last by apply H_in_s1'_s2.
      move => [] H_y1_le H_x1_lt H_x2_in.
      move : H_gr.
      rewrite interval_list_elements_greater_alt2_def; last first. {
          by apply interval_list_invariant_app_intro.
      }
      move => H_in_s12'.
      have : (y1 + Z.of_N c1 < x2). {
        apply H_in_s12'.
        rewrite InZ_app.
        by right.
      }
      move => H_lt_x2.
      apply Z.le_lt_trans with (m := y1 + Z.of_N c1) => //.
      by apply Zlt_le_succ.
    }
  Qed.

  Lemma interval_list_invariant_app_iff : forall s1 s2,
      interval_list_invariant (s1 ++ s2) = true <->
      (interval_list_invariant s1 = true /\
      interval_list_invariant s2 = true /\
      (forall (x1 x2 : Z), InZ x1 s1 -> InZ x2 s2 -> Z.succ x1 < x2)).
  Proof.
    intros s1 s2.
    split. {
      by apply interval_list_invariant_app_elim.
    } {
      move => [] H_inv_s1 [].
      by apply interval_list_invariant_app_intro.
    }
  Qed.

  Lemma interval_list_invariant_snoc_intro : forall s1 y2 c2,
      interval_list_invariant s1 = true ->
      (c2 <> 0)%N ->
      (forall x, InZ x s1 -> Z.succ x < y2) ->
      interval_list_invariant (s1 ++ ((y2, c2)::nil)) = true.
  Proof.
    intros s1 y2 c2 H_inv_s1 H_c2_neq H_in_s1.
    apply interval_list_invariant_app_intro => //. {
      rewrite interval_list_invariant_cons; done.
    } {
      intros x1 x2 H_in_x1.
      rewrite InZ_cons.
      move => [] //.
      rewrite In_elementsZ_single.
      move => [H_y2_le] _.
      eapply Z.lt_le_trans; eauto.
    }
  Qed.

    
  (** *** Properties of In and InZ *)

  Lemma encode_decode_eq : forall x s, Ok s -> InZ x s ->
    (Enc.encode (Enc.decode x) = x).
  Proof.
    intros x s.
    rewrite /Ok /IsOk /InZ.
    move => [_] H_enc H_in_x.
    move : (H_enc _ H_in_x) => [x'] <-.
    rewrite Enc.decode_encode_ok //.
  Qed.

  Lemma In_alt_def : forall x s, Ok s -> 
    (In x s <-> List.In x (elements s)).
  Proof.
    intros x s H_ok.
    rewrite /In InA_alt /elements rev_map_alt_def.
    split. {
      move => [y] [H_y_eq].
      rewrite -!in_rev !in_map_iff.      
      move => [x'] [H_y_eq'] H_x'_in.
      suff H_x'_eq :  (Enc.encode x = x'). {
        exists x'.
        split => //.
        rewrite -H_x'_eq Enc.decode_encode_ok //.
      }
      have H_enc_list : is_encoded_elems_list (elementsZ s). {
        move : H_ok.
        rewrite /Ok /IsOk => [] [] //.
      } 
      move : (H_enc_list _ H_x'_in) => [x''] H_x'_eq.
      move : H_y_eq'.
      rewrite -!H_x'_eq Enc.decode_encode_ok => H_y_eq'.
      subst.
      suff -> : Z.eq (Enc.encode x) (Enc.encode y) by done.
      by rewrite Enc.encode_eq.
    } {
      move => H_enc_in.
      exists x.
      split => //. 
      apply Enc.E.eq_equiv.
    }
  Qed.

  Lemma In_InZ : forall x s, Ok s -> 
    (In x s <-> InZ (Enc.encode x) s).
  Proof.
    intros x s H_ok.
    rewrite /InZ In_alt_def /elements rev_map_alt_def -in_rev in_map_iff.
    split; last first. {
      exists (Enc.encode x).
      by rewrite Enc.decode_encode_ok.
    }
    move => [y] [<-] H_y_in. 
    suff : exists z, (Enc.encode z = y). {
      move => [z] H_y_eq.
      move : H_y_in.
      by rewrite -!H_y_eq Enc.decode_encode_ok.
    }
    suff H_enc_list : is_encoded_elems_list (elementsZ s). {
      by apply H_enc_list.
    }
    apply H_ok.
  Qed.

  Lemma InZ_In : forall x s, Ok s -> 
    (InZ x s -> In (Enc.decode x) s).
  Proof.
    intros x s H_ok.
    rewrite In_InZ /InZ.
    move : H_ok.
    rewrite /Ok /IsOk /is_encoded_elems_list.
    move => [_] H_enc.
    move => H_in.
    move : (H_enc _ H_in) => [e] H_x.
    subst.
    by rewrite Enc.decode_encode_ok.
  Qed.

  
  (** *** Membership specification *)
          
  Lemma memZ_spec :
    forall (s : t) (x : Z) (Hs : Ok s), memZ x s = true <-> InZ x s.
  Proof.
    induction s as [| [y c] s' IH]. {
      intros x _.
      rewrite /InZ elementsZ_nil //.
    } {    
      move => x /Ok_cons [H_inf] [H_c] [H_is_enc] H_s'.  
      rewrite /InZ /memZ elementsZ_cons -/memZ.
      rewrite in_app_iff -!in_rev In_elementsZ_single.

      case_eq (x <? y). {
        move => /Z.ltb_lt H_x_lt.
        split; first done.
        move => []. {
          move => H_x_in; contradict H_x_in.
          apply Nin_elements_greater with (y := (y + Z.of_N c)) => //. {
            apply H_s'.
          } {
            apply Z_lt_le_add_r => //.
          }
        } {
          move => [H_y_le]; contradict H_y_le.
          by apply Z.nle_gt.
        }
      } {
        move => /Z.ltb_ge H_y_le.
        case_eq (x <? y + Z.of_N c). {
          move => /Z.ltb_lt H_x_lt.
          split; last done.
          move => _.
          by right.
        } {
          move => /Z.ltb_ge H_yc_le.
          rewrite IH.
          split; first tauto.
          move => [] //.
          move => [_] H_x_lt; contradict H_x_lt.
          by apply Z.nlt_ge.
        }
      }
    }
  Qed.   

  Lemma mem_spec :
   forall (s : t) (x : elt) (Hs : Ok s), mem x s = true <-> In x s.
  Proof.
    intros s x Hs.
    rewrite /mem memZ_spec In_InZ //.
  Qed.

  Lemma merge_interval_size_neq_0 : forall x1 c1 x2 c2,
     (c1 <> 0%N) ->
     (merge_interval_size x1 c1 x2 c2 <> 0)%N.
  Proof.
    intros x1 c1 x2 c2.
    rewrite /merge_interval_size !N.neq_0_lt_0 N.max_lt_iff.
    by left.
  Qed.


  (** *** insert if length not 0 *)

  Lemma interval_list_invariant_insert_intervalZ_guarded : forall x c s,
    interval_list_invariant s = true -> 
    interval_list_elements_greater (x + Z.of_N c) s = true ->
    interval_list_invariant (insert_intervalZ_guarded x c s) = true.
  Proof.
    intros x c s.
    rewrite /insert_intervalZ_guarded.
    case_eq (c =? 0)%N => //.
    move => /N.eqb_neq.
    rewrite interval_list_invariant_cons.
    tauto.
  Qed.

  Lemma interval_list_elements_greater_insert_intervalZ_guarded : forall x c y s,
    interval_list_elements_greater y (insert_intervalZ_guarded x c s) = true <->
    (if (c =? 0)%N then (interval_list_elements_greater y s = true) else (y < x)).
  Proof.
    intros x c y s.
    rewrite /insert_intervalZ_guarded.
    case (c =? 0)%N => //.       
    rewrite /interval_list_elements_greater Z.ltb_lt //.
  Qed.

  Lemma insert_intervalZ_guarded_app : forall x c s1 s2,
    (insert_intervalZ_guarded x c s1) ++ s2 =
    insert_intervalZ_guarded x c (s1 ++ s2).
  Proof.
    intros x c s1 s2.
    rewrite /insert_intervalZ_guarded.
    case (N.eqb c 0) => //.
  Qed.

  Lemma insert_intervalZ_guarded_rev_nil_app : forall x c s,
    rev (insert_intervalZ_guarded x c nil) ++ s =
    insert_intervalZ_guarded x c s.
  Proof.
    intros x c s.
    rewrite /insert_intervalZ_guarded.
    case (N.eqb c 0) => //.
  Qed.

Lemma elementsZ_insert_intervalZ_guarded : forall x c s,
    elementsZ (insert_intervalZ_guarded x c s) = elementsZ ((x, c) :: s). 
  Proof.
    intros x c s.
    rewrite /insert_intervalZ_guarded.
    case_eq (c =? 0)%N => //.
    move => /N.eqb_eq ->.
    rewrite elementsZ_cons elementsZ_single_base /= app_nil_r //.
  Qed.

  Lemma InZ_insert_intervalZ_guarded : forall y x c s,
    InZ y (insert_intervalZ_guarded x c s) = InZ y ((x, c) :: s). 
  Proof.
    intros y x c s.
    rewrite /InZ elementsZ_insert_intervalZ_guarded //.
  Qed.
  
  (** *** Merging intervals *)

  Lemma merge_interval_size_add : forall x c1 c2,
     (merge_interval_size x c1 (x + Z.of_N c1) c2 = (c1 + c2))%N.
  Proof.
    intros x c1 c2.
    rewrite /merge_interval_size.
    replace (x + Z.of_N c1 + Z.of_N c2 - x) with
            (Z.of_N c1 + Z.of_N c2) by omega.
    rewrite -N2Z.inj_add N2Z.id.
    apply N.max_r, N.le_add_r.
  Qed.

  Lemma merge_interval_size_eq_max : forall y1 c1 y2 c2,
     y1 <= y2 + Z.of_N c2 ->
     y1 + Z.of_N (merge_interval_size y1 c1 y2 c2) = 
     Z.max (y1 + Z.of_N c1) (y2 + Z.of_N c2).
  Proof.
    intros y1 c1 y2 c2 H_y1_le.
    rewrite /merge_interval_size N2Z.inj_max Z2N.id; last first. {
      by apply Zle_minus_le_0.
    }
    rewrite -Z.add_max_distr_l.
    replace (y1 + (y2 + Z.of_N c2 - y1)) with (y2 + Z.of_N c2) by omega.
    done.
  Qed.

  Lemma merge_interval_size_invariant : forall y1 c1 y2 c2 z s,
    interval_list_invariant s = true ->
    y1 + Z.of_N c1 <= y2 + Z.of_N c2 ->
    y2 + Z.of_N c2 <= z ->
    interval_list_elements_greater z s = true ->
    (c1 <> 0)%N ->
    interval_list_invariant ((y1, merge_interval_size y1 c1 y2 c2) :: s) =
   true.
  Proof.
    intros y1 c1 y2 c2 z s H_inv H_le H_le_z H_gr H_c1_neq_0.
    rewrite interval_list_invariant_cons.
    split; last split. {
      rewrite merge_interval_size_eq_max; last first. {
        eapply Z.le_trans; last apply H_le.
        apply Z_le_add_r.
      } {
        rewrite Z.max_r => //.
        eapply interval_list_elements_greater_impl; first apply H_le_z.
        done.
      }
    } {
      apply merge_interval_size_neq_0.
      assumption.
    } {
      assumption.
    }
  Qed.


  Lemma In_merge_interval : forall x1 c1 x2 c2 y,
    x1 <= x2 -> 
    x2 <= x1 + Z.of_N c1 -> (
    List.In y (elementsZ_single x1 (merge_interval_size x1 c1 x2 c2)) <->
    List.In y (elementsZ_single x1 c1) \/ List.In y (elementsZ_single x2 c2)).
  Proof.
    intros x1 c1 x2 c2 y H_x1_le H_x2_le.
    rewrite !In_elementsZ_single merge_interval_size_eq_max; 
      last first. {
      eapply Z.le_trans; eauto.
      by apply Z_le_add_r.
    }
    rewrite Z.max_lt_iff.
    split. {
      move => [H_x_le] [] H_y_lt. {
        by left.
      } {
        case_eq (Z.leb x2 y). {
          move => /Z.leb_le H_y'_le.
          by right.
        } {
          move => /Z.leb_gt H_y_lt_x2.
          left.
          split => //.
          eapply Z.lt_le_trans; eauto.
        }
      }
    } {
      move => []. {
        tauto.
      } {
        move => [H_x2_le'] H_y_lt.
        split. {
          eapply Z.le_trans; eauto.
        } {
          by right.
        }
      }
    }
  Qed.

  Lemma insert_interval_begin_spec : forall y s x c,
     interval_list_invariant s = true -> 
     interval_list_elements_greater x s = true ->
     (c <> 0)%N ->
      (
     interval_list_invariant (insert_interval_begin x c s) = true /\
     (InZ y (insert_interval_begin x c s) <->
     (List.In y (elementsZ_single x c) \/ InZ y s))).
  Proof.
    intros y.
    induction s as [| [y' c'] s' IH]. {
      intros x c _ H_c_neq H_z_lt.
      rewrite /insert_interval_begin InZ_cons interval_list_invariant_cons //.
    } {
      intros x c.
      rewrite interval_list_invariant_cons
       interval_list_elements_greater_cons.
      move => [H_gr] [H_c'_neq_0] H_inv_s' H_x_lt H_c_neq_0.
      unfold insert_interval_begin.
      Z_named_compare_cases H_y'; fold insert_interval_begin. {
        subst.
        rewrite !InZ_cons elementsZ_single_add in_app_iff.
        split; last tauto.
        rewrite interval_list_invariant_cons N2Z.inj_add
          Z.add_assoc N.eq_add_0.
        tauto.
      } {
        rewrite !InZ_cons !interval_list_invariant_cons
          interval_list_elements_greater_cons.
        repeat split => //.
      } {
        set c'' := merge_interval_size x c y' c'.
        have H_x_lt' : x < y' + Z.of_N c'. {
          eapply Z.lt_le_trans with (m := y') => //. 
          by apply Z_le_add_r.
        } 

        have H_pre : interval_list_elements_greater x s' = true. {
          eapply interval_list_elements_greater_impl; eauto.
          by apply Z.lt_le_incl.
        }
        have H_pre2 : c'' <> 0%N. {
          by apply merge_interval_size_neq_0.
        }
        move : (IH x c'' H_inv_s' H_pre H_pre2) => {IH} {H_pre} {H_pre2} [->] ->.

        split; first reflexivity.
        unfold c''; clear c''.
        rewrite In_merge_interval. {
          rewrite InZ_cons. 
          tauto.
        } {
          by apply Z.lt_le_incl.
        } {
          by apply Z.lt_le_incl.
        }
      }
    }
  Qed.


  (** *** add specification *)
  Lemma addZ_InZ :
   forall (s : t) (x y : Z),
    interval_list_invariant s = true ->
    (InZ y (addZ x s) <-> x = y \/ InZ y s).
  Proof.
    move => s x y.
    induction s as [| [z c] s' IH]. {
      move => _.
      rewrite /InZ addZ_alt_def
              elementsZ_cons elementsZ_nil app_nil_l -in_rev
              In_elementsZ_single1 /=.
      firstorder.
    } {
      move => /interval_list_invariant_cons [H_greater] [H_c_neq_0] H_inv_c'.
      move : (IH H_inv_c') => {IH} IH.
      rewrite addZ_alt_def.
      have H_succ : forall z, z + Z.of_N 1 = Z.succ z by done.
      move : (interval_1_compare_elim x z c).      
      case (interval_1_compare x (z, c));
        rewrite ?InZ_cons ?In_elementsZ_single1 ?H_succ ?Z.lt_succ_r //. {
        move => ->.
        rewrite elementsZ_single_succ_front /=.
        tauto.
      } {
        move => [] // H_x_in.
        split; first tauto.
        move => [] // <-.
        left.
        by rewrite In_elementsZ_single.
      } {
        rewrite IH.
        tauto.
      } {
        move => H_x_eq.
        have -> : (InZ y (insert_interval_begin z (N.succ c) s') <->
                   List.In y (elementsZ_single z (N.succ c)) \/ InZ y s'). {
          eapply insert_interval_begin_spec. {
            by apply H_inv_c'.
          } {
            eapply interval_list_elements_greater_impl; eauto.
            apply Z_le_add_r.
          } {
            by apply N.neq_succ_0.
          }
        }
        rewrite -H_x_eq elementsZ_single_succ in_app_iff /=.
        tauto.
      }
    }
  Qed.

  Lemma addZ_invariant : forall s x, 
    interval_list_invariant s = true -> 
    interval_list_invariant (addZ x s) = true.
  Proof. 
    move => s x.
    induction s as [| [z c] s' IH]. {
      move => _.
      by simpl.
    } {
      move => /interval_list_invariant_cons [H_greater] [H_c_neq_0]
              H_inv_c'.
      move : (IH H_inv_c') => {IH} IH.
      rewrite addZ_alt_def.
      have H_succ : forall z, z + Z.of_N 1 = Z.succ z by done.
      move : (interval_1_compare_elim x z c).      
      case_eq (interval_1_compare x (z, c)) => H_comp;
        rewrite ?InZ_cons ?In_elementsZ_single1 ?H_succ ?Z.lt_succ_r //. {
        move => H_z_gt.
        rewrite interval_list_invariant_cons /= !andb_true_iff !H_succ.
        repeat split => //. {
          by apply Z.ltb_lt.
        } {
          apply negb_true_iff, N.eqb_neq => //.
        }
      } {
        move => ?; subst.
        rewrite /= !andb_true_iff.
        repeat split => //. {
          move : H_greater.
          rewrite Z.add_succ_l -Z.add_succ_r N2Z.inj_succ //.
        } {
          apply negb_true_iff, N.eqb_neq => //.
          apply N.neq_succ_0.
        }
      } {
        move => [] // _.
        rewrite interval_list_invariant_cons /=.
        tauto.
      } {
        rewrite interval_list_invariant_cons.
        move => H_lt_x.
        repeat split => //.
        apply interval_list_elements_greater_intro => //.
        move => xx.
        rewrite addZ_InZ => //.
        move => [<- //|]. 
        apply interval_list_elements_greater_alt2_def => //.
      } {
        move => H_x_eq.
        apply insert_interval_begin_spec => //. {
          eapply interval_list_elements_greater_impl; eauto.
          apply Z_le_add_r.
        } {
          by apply N.neq_succ_0.
        }
      }
    }
  Qed.
  
  Global Instance add_ok s x : forall `(Ok s), Ok (add x s).
  Proof. 
    move => H_ok_s.
    move : (H_ok_s).
    rewrite /Ok /IsOk /is_encoded_elems_list /add.
    move => [H_isok_s] H_pre.
    split. {
      apply addZ_invariant => //.
    } {
      intros y.
      move : (addZ_InZ s (Enc.encode x) y H_isok_s).
      rewrite /InZ => ->.
      move => []. {
        move => <-.
        by exists x.
      } {
        move => /H_pre //.
      }
    }
  Qed.
    
  Lemma add_spec :
   forall (s : t) (x y : elt) (Hs : Ok s),
     In y (add x s) <-> Enc.E.eq y x \/ In y s.
  Proof.
    intros s x y Hs.
    have Hs' := (add_ok s x Hs).
    rewrite !In_InZ.
    rewrite /add addZ_InZ. {
      rewrite -Enc.encode_eq; firstorder.
    } {
      apply Hs.
    }
  Qed.


  (** *** empty specification *)

  Global Instance empty_ok : Ok empty.
  Proof.
    rewrite /empty Ok_nil //.
  Qed.

  Lemma empty_spec' : forall x, (In x empty <-> False).
    rewrite /Empty /empty /In elements_nil.
    intros a.
    rewrite InA_nil //.
  Qed.

  Lemma empty_spec : Empty empty.
  Proof.
    rewrite /Empty => a.
    rewrite empty_spec' //.
  Qed.

  (** *** is_empty specification *)

  Lemma is_empty_spec : forall (s : t) (Hs : Ok s), is_empty s = true <-> Empty s.
  Proof.
    intros [ | [x c] s]. {
      split => // _.
      apply empty_spec.
    } {
      rewrite /= /Empty Ok_cons.
      move => [_] [H_c_neq] [H_enc] _.
      split => //.
      move => H.
      contradiction (H (Enc.decode x)) => {H}.
      rewrite /In InA_alt elements_cons.
      exists (Enc.decode x).
      split; first by apply Enc.E.eq_equiv.
      rewrite in_app_iff; left.
      rewrite /elements_single in_map_iff.
      exists x.
      split => //.
      apply In_elementsZ_single_hd => //.
    }
  Qed.


  (** *** singleton specification *)

  Global Instance singleton_ok x : Ok (singleton x).
  Proof.
    rewrite singleton_alt_def.
    apply add_ok.
    apply empty_ok.
  Qed.

  Lemma singleton_spec : forall x y : elt, In y (singleton x) <-> Enc.E.eq y x.
  Proof.
    intros x y.
    rewrite singleton_alt_def.
    rewrite (add_spec empty x y) /empty /In elements_nil InA_nil.
    split. {
      move => [] //.
    } {
      by left.
    }
  Qed.

  (** *** add_list specification *)

  Lemma add_list_ok : forall l s, Ok s -> Ok (add_list l s).
  Proof.
    induction l as [| x l' IH]. {
      done.
    } {
      move => s H_s_ok /=.
      apply IH.
      by apply add_ok.
    }
  Qed.

  Lemma add_list_spec : forall x l s, Ok s -> 
     (In x (add_list l s) <-> (SetoidList.InA Enc.E.eq x l) \/ In x s).
  Proof.
    move => x.
    induction l as [| y l' IH]. {
      intros s H.
      rewrite /= InA_nil.
      tauto.
    } {
      move => s H_ok /=.
      rewrite IH add_spec InA_cons.
      tauto.
    }
  Qed.

  (** *** union specification *)

  Lemma union_aux_flatten_alt_def : forall (s1 s2 : t) acc, 
    union_aux s1 s2 acc =
    match (s1, s2) with
    | (nil, _) => List.rev_append acc s2
    | (_, nil) => List.rev_append acc s1
    | ((y1, c1) :: l1, (y2, c2) :: l2) =>
        match (interval_compare (y1, c1) (y2,c2)) with
          | ICR_before       => union_aux l1 s2 ((y1, c1)::acc)
          | ICR_before_touch => 
              union_aux l1 (
                insert_interval_begin y1 ((c1+c2)%N) l2) acc
          | ICR_after        => union_aux s1 l2 ((y2, c2)::acc)
          | ICR_after_touch  => union_aux l1 (
              insert_interval_begin y2 ((c1+c2)%N) l2) acc
          | ICR_overlap_before => 
              union_aux l1 (
                insert_interval_begin y1 
                  (merge_interval_size y1 c1 y2 c2) l2) acc
          | ICR_overlap_after => 
              union_aux l1 (
                insert_interval_begin y2 
                  (merge_interval_size y2 c2 y1 c1) l2) acc
          | ICR_equal => union_aux l1 s2 acc
          | ICR_subsume_1 => union_aux l1 s2 acc
          | ICR_subsume_2 => union_aux s1 l2 acc
        end
    end.
  Proof.
    intros s1 s2 acc.    
    case s1, s2 => //. 
  Qed.

  Lemma union_aux_alt_def : forall (s1 s2 : t) acc, 
    union_aux s1 s2 acc =
    List.rev_append acc (union s1 s2).
  Proof.
    rewrite /union.
    intros s1 s2 acc.
    move : acc s2.
    induction s1 as [| [y1 c1] l1 IH1]. {
      intros acc s2.
      rewrite !union_aux_flatten_alt_def.
      rewrite !rev_append_rev //.
    }
    intros acc s2; move : acc.
    induction s2 as [| [y2 c2] l2 IH2]; first by simpl.
    move => acc.
    rewrite !(union_aux_flatten_alt_def ((y1, c1)::l1) ((y2, c2)::l2)).
    case (interval_compare (y1, c1) (y2, c2));
      rewrite ?(IH1 ((y1, c1) :: acc)) ?(IH1 ((y1, c1) :: nil))
              ?(IH2 ((y2, c2) :: acc)) ?(IH2 ((y2, c2) :: nil))
              ?(IH1 acc) //.
  Qed.

  Lemma union_alt_def : forall (s1 s2 : t), 
    union s1 s2 =
    match (s1, s2) with
    | (nil, _) => s2
    | (_, nil) => s1
    | ((y1, c1) :: l1, (y2, c2) :: l2) =>
        match (interval_compare (y1, c1) (y2,c2)) with
          | ICR_before       => (y1, c1) :: (union l1 s2)
          | ICR_before_touch => 
              union l1 (insert_interval_begin y1 ((c1+c2)%N) l2)
          | ICR_after        => (y2, c2) :: union s1 l2
          | ICR_after_touch  => union l1 
              (insert_interval_begin y2 ((c1+c2)%N) l2)
          | ICR_overlap_before => 
              union l1 (insert_interval_begin y1 (merge_interval_size y1 c1 y2 c2) l2)
          | ICR_overlap_after => 
              union l1 (insert_interval_begin y2 (merge_interval_size y2 c2 y1 c1) l2)
          | ICR_equal => union l1 s2 
          | ICR_subsume_1 => union l1 s2 
          | ICR_subsume_2 => union s1 l2
        end
     end.
  Proof.
    intros s1 s2.
    rewrite /union union_aux_flatten_alt_def.
    case s1 as [| [y1 c1] l1] => //.
    case s2 as [| [y2 c2] l2] => //.
    case (interval_compare (y1, c1) (y2, c2));
      rewrite union_aux_alt_def //.
  Qed.

  Lemma union_InZ :
   forall (s1 s2 : t),
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    forall y, (InZ y (union s1 s2) <-> InZ y s1 \/ InZ y s2).
  Proof.
    intro s1.
    induction s1 as [| [y1 c1] l1 IH1]. {
      intros s2 _ _ y.
      rewrite union_alt_def /InZ /=.
      tauto.
    } {
      induction s2 as [| [y2 c2] l2 IH2]. {
        intros _ _ y.
        rewrite union_alt_def /InZ /=.
        tauto.
      } {
        move => H_inv_s1 H_inv_s2.
        move : (H_inv_s1) (H_inv_s2).
        rewrite !interval_list_invariant_cons.
        move => [H_gr_l1] [H_c1_neq_0] H_inv_l1.
        move => [H_gr_l2] [H_c2_neq_0] H_inv_l2.
        move : (IH2 H_inv_s1 H_inv_l2) => {IH2} IH2.
        have :  forall s2 : t,
          interval_list_invariant s2 = true ->
          forall y : Z, InZ y (union l1 s2) <-> InZ y l1 \/ InZ y s2. {
          intros. by apply IH1.
        }
        move => {IH1} IH1 y.
        rewrite union_alt_def.
        move : (interval_compare_elim y1 c1 y2 c2).
        case (interval_compare (y1, c1) (y2, c2)). {
          rewrite !InZ_cons IH1 // InZ_cons.
          tauto.
        } {
          move => H_y2_eq.
          replace (c1 + c2)%N with (merge_interval_size y1 c1 y2 c2);
            last first. {
            rewrite -H_y2_eq merge_interval_size_add //.
          }
          set c'' := merge_interval_size y1 c1 y2 c2.
          have [H_inv_insert H_InZ_insert] : 
               interval_list_invariant (insert_interval_begin y1 c'' l2) = true /\
                (InZ y (insert_interval_begin y1 c'' l2) <->
                List.In y (elementsZ_single y1 c'') \/ InZ y l2). {
            apply insert_interval_begin_spec => //. {
              eapply interval_list_elements_greater_impl; eauto.
              rewrite -H_y2_eq -Z.add_assoc -N2Z.inj_add.
              apply Z_le_add_r.
            } {
              by apply merge_interval_size_neq_0.
            } 
          }
  
          rewrite IH1 => //.
          rewrite H_InZ_insert !InZ_cons /c''.
          rewrite -H_y2_eq In_merge_interval. {
            tauto.
          } {
            apply Z_le_add_r.
          } {
            by apply Z.le_refl.
          }
        } {
          move => [H_y1_lt] [H_y2_lt] H_y1_c1_lt.
          set c'' := merge_interval_size y1 c1 y2 c2.
          have [H_inv_insert H_InZ_insert] : 
               interval_list_invariant (insert_interval_begin y1 c'' l2) = true /\
                (InZ y (insert_interval_begin y1 c'' l2) <->
                List.In y (elementsZ_single y1 c'') \/ InZ y l2). {
            apply insert_interval_begin_spec => //. {
              eapply interval_list_elements_greater_impl; eauto.
              apply Z_lt_le_add_r => //.
            } {
              by apply merge_interval_size_neq_0.
            } 
          }
          rewrite IH1 => //.
          rewrite H_InZ_insert !InZ_cons /c''.
          rewrite In_merge_interval. {
            tauto.
          } {
            by apply Z.lt_le_incl.
          } {
            by apply Z.lt_le_incl.
          }
        } {
          move => [H_y2_lt] [H_y1_lt] H_y2_c_lt.
          set c'' := merge_interval_size y2 c2 y1 c1.
          have [H_inv_insert H_InZ_insert] : 
               interval_list_invariant (insert_interval_begin y2 c'' l2) = true /\
                (InZ y (insert_interval_begin y2 c'' l2) <->
                List.In y (elementsZ_single y2 c'') \/ InZ y l2). {
            apply insert_interval_begin_spec => //. {
              eapply interval_list_elements_greater_impl; eauto.
              apply Z_le_add_r.
            } {
              by apply merge_interval_size_neq_0.
            } 
          }
  
          rewrite IH1 => //.
          rewrite H_InZ_insert !InZ_cons /c''.
          rewrite In_merge_interval. {
            tauto.
          } {
            by apply Z.lt_le_incl.
          } {
            by apply Z.lt_le_incl.
          }
        } {
          move => [? ?]; subst.
          rewrite IH1 => //.
          rewrite !InZ_cons. 
          tauto.
        } {
          move => [H_y2_le] [H_y1_c1_le] _.
          rewrite IH1 => //.
          rewrite !InZ_cons. 
          suff : (List.In y (elementsZ_single y1 c1) ->
                  List.In y (elementsZ_single y2 c2)). {
            tauto.
          }
          rewrite !In_elementsZ_single.
          move => [H_y1_le H_y_lt].
          split; omega.
        } {
          move => [H_y1_le] [H_y2_c2_le] _.
          rewrite IH2.
          rewrite !InZ_cons. 
          suff : (List.In y (elementsZ_single y2 c2) ->
                  List.In y (elementsZ_single y1 c1)). {
            tauto.
          }
          rewrite !In_elementsZ_single.
          move => [H_y2_le H_y_lt].
          split; omega.
        } {
          rewrite !InZ_cons IH2 !InZ_cons.
          tauto.
        } {
          move => H_y1_eq.
          replace (c1 + c2)%N with (merge_interval_size y2 c2 y1 c1);
            last first. {
            rewrite -H_y1_eq merge_interval_size_add N.add_comm //.
          }
          set c'' := merge_interval_size y2 c2 y1 c1.
          have [H_inv_insert H_InZ_insert] : 
               interval_list_invariant (insert_interval_begin y2 c'' l2) = true /\
                (InZ y (insert_interval_begin y2 c'' l2) <->
                List.In y (elementsZ_single y2 c'') \/ InZ y l2). {
            apply insert_interval_begin_spec => //. {
              eapply interval_list_elements_greater_impl; eauto.
              apply Z_le_add_r.
            } {
              by apply merge_interval_size_neq_0.
            } 
          }
  
          rewrite IH1 => //.
          rewrite H_InZ_insert !InZ_cons /c''.
          rewrite -H_y1_eq In_merge_interval. {
            tauto.
          } {
            apply Z_le_add_r.
          } {
            by apply Z.le_refl.
          }
        }
      }
    }
  Qed.

  Lemma union_invariant :
   forall (s1 s2 : t),
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    interval_list_invariant (union s1 s2) = true.
  Proof.
    intro s1.
    induction s1 as [| [y1 c1] l1 IH1]. {
      intros s2 _ H_inv_s2.
      rewrite union_alt_def /InZ //.
    } {
      induction s2 as [| [y2 c2] l2 IH2]. {
        intros H_inv_s1 _.
        rewrite union_alt_def /InZ //.
      } {
        move => H_inv_s1 H_inv_s2.
        move : (H_inv_s1) (H_inv_s2).
        rewrite !interval_list_invariant_cons.
        move => [H_gr_l1] [H_c1_neq_0] H_inv_l1.
        move => [H_gr_l2] [H_c2_neq_0] H_inv_l2.
        move : (IH2 H_inv_s1 H_inv_l2) => {IH2} IH2.
        have :  forall s2 : t,
          interval_list_invariant s2 = true ->
          interval_list_invariant (union l1 s2) = true. {
          intros. by apply IH1.
        }
        move => {IH1} IH1.

        rewrite union_alt_def.
        move : (interval_compare_elim y1 c1 y2 c2).
        case (interval_compare (y1, c1) (y2, c2)). {
          move => H_lt_y2.
          have H_inv' : interval_list_invariant (union l1 ((y2, c2) :: l2)) = true. {
            by apply IH1.
          }

          rewrite interval_list_invariant_cons.
          repeat split => //. 
          apply interval_list_elements_greater_intro => // x.
          rewrite union_InZ => //.
          move => []. {
            apply interval_list_elements_greater_alt2_def => //.
          } {
            apply interval_list_elements_greater_alt2_def => //.
            rewrite interval_list_elements_greater_cons //.
          }
        } {
          move => H_y2_eq.
          apply IH1.
          apply insert_interval_begin_spec => //. {
            eapply interval_list_elements_greater_impl; last apply H_gr_l2.
            rewrite -H_y2_eq -Z.add_assoc -N2Z.inj_add.
            apply Z_le_add_r.
          } {
            rewrite N.eq_add_0.
            tauto.
          }
        } {
          move => [H_y1_lt] _.
          apply IH1. 
          apply insert_interval_begin_spec => //. {
            eapply interval_list_elements_greater_impl; last apply H_gr_l2.
            apply Z_lt_le_add_r => //.
          } {
            apply merge_interval_size_neq_0 => //.
          }
        } {
          move => [H_y2_lt] _.
          apply IH1.
          apply insert_interval_begin_spec => //. {
            eapply interval_list_elements_greater_impl; last apply H_gr_l2.
            apply Z_le_add_r => //.
          } {
            apply merge_interval_size_neq_0 => //.
          }
        } {
          move => [? ?]; subst.
          apply IH1 => //. 
        } {
          move => _.
          apply IH1 => //. 
        } {
          move => _.
          apply IH2 => //. 
        } {
          move => H_lt_y1.
          rewrite interval_list_invariant_cons => //.
          repeat split => //.
          apply interval_list_elements_greater_intro => // x.
          rewrite union_InZ => //.
          move => []. {
            apply interval_list_elements_greater_alt2_def => //.
            rewrite interval_list_elements_greater_cons //.
          } {
            apply interval_list_elements_greater_alt2_def => //.
          }
        } {
          move => H_y1_eq.
          apply IH1 => //.
          apply insert_interval_begin_spec => //. {
            eapply interval_list_elements_greater_impl; last apply H_gr_l2.
            apply Z_le_add_r.
          } {
            rewrite N.eq_add_0.
            tauto.
          }
        }
      }
    }
  Qed.

 
  Global Instance union_ok s1 s2 : forall `(Ok s1, Ok s2), Ok (union s1 s2).
  Proof.
    move => H_ok_s1 H_ok_s2.
    move : (H_ok_s1) (H_ok_s2).
    rewrite /Ok /IsOk /is_encoded_elems_list /add.
    move => [H_inv_s1] H_pre1.
    move => [H_inv_s2] H_pre2.
    split. {
      apply union_invariant => //.
    } {
      intros y.
      move : (union_InZ s1 s2 H_inv_s1 H_inv_s2).    
      rewrite /InZ => ->.      
      move => []. {
        apply H_pre1.
      } {
        apply H_pre2.
      }
    }
  Qed.

  Lemma union_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (union s s') <-> In x s \/ In x s'.
  Proof.
    intros s s' x H_ok H_ok'.
    rewrite !In_InZ.
    rewrite union_InZ => //. {
      apply H_ok.
    } {
      apply H_ok'.
    }
  Qed.


  (** *** inter specification *)
 
  Lemma inter_aux_alt_def :
    forall (y2 : Z) (c2 : N) (s : t) acc,
      inter_aux y2 c2 acc s = match inter_aux y2 c2 nil s with
                               (acc', s') => (acc' ++ acc, s')
                             end.
  Proof.
    intros y2 c2.
    induction s as [| [y1 c1] s' IH] => acc. {
      rewrite /inter_aux app_nil_l //.
    } {
      simpl.
      case_eq (inter_aux y2 c2 nil s') => acc'' s'' H_eq.
      case (interval_compare (y1, c1) (y2, c2));
        rewrite ?(IH acc)
                ?(IH ((y2, Z.to_N (y1 + Z.of_N c1 - y2)) :: acc))
                ?(IH ((y2, Z.to_N (y1 + Z.of_N c1 - y2)) :: nil))
                ?(IH ((y1, Z.to_N (y2 + Z.of_N c2 - y1)) :: acc))
                ?(IH ((y1, Z.to_N (y2 + Z.of_N c2 - y1)) :: nil))
                ?(IH ((y1, c1) :: acc))
                ?(IH ((y1, c1) :: nil))
                
                ?H_eq -?app_assoc -?app_comm_cons //.     
    }
  Qed.

  Lemma inter_aux_props :
    forall (y2 : Z) (c2 : N) (s : t) acc,
      interval_list_invariant (rev acc) = true ->
      interval_list_invariant s = true ->
      (forall x1 x2, InZ x1 acc -> InZ x2 s ->
                     List.In x2 (elementsZ_single y2 c2) ->
                     Z.succ x1 < x2) ->
      (c2 <> 0%N) ->
      match (inter_aux y2 c2 acc s) with (acc', s') =>
        (forall y, (InZ y acc' <->
                   (InZ y acc \/ (InZ y s /\ (List.In y (elementsZ_single y2 c2)))))) /\
        (forall y, InZ y s' -> InZ y s) /\
        (forall y, InZ y s -> y2 + Z.of_N c2 < y -> InZ y s') /\
        interval_list_invariant (rev acc') = true /\
        interval_list_invariant s' = true
      end.
  Proof.
    intros y2 c2.     
    induction s as [| [y1 c1] s1' IH] => acc. {
      rewrite /inter_aux.       
      move => H_inv_acc _ _ _.
      split; last split; try done.
      move => y. rewrite InZ_nil.
      tauto.
    } {
      rewrite interval_list_invariant_cons.       
      move => H_inv_acc [H_gr_s1'] [H_c1_neq_0] H_inv_s1'.
      move => H_in_acc_lt H_c2_neq_0.
       
      rewrite inter_aux_alt_def.
      case_eq (inter_aux y2 c2 nil ((y1, c1) :: s1')).
      move => acc' s' H_inter_aux_eq.

      set P1 := forall y : Z,
        (InZ y acc' <->
        ((InZ y ((y1, c1) :: s1') /\ List.In y (elementsZ_single y2 c2)))).
      set P2 := (forall y,
                  (InZ y s' -> InZ y ((y1, c1) :: s1')) /\
                  (InZ y ((y1, c1) :: s1') ->
                     y2 + Z.of_N c2 < y -> InZ y s')).
      set P3 := interval_list_invariant (rev acc') = true.
      set P4 := interval_list_invariant s' = true.

      suff : (P1 /\ P2 /\ P3 /\ P4). {
        move => [H_P1] [H_P2] [H_P3] H_P4.
        split; last split; last split; last split. {
          move => y.
          move : (H_P1 y).
          rewrite !InZ_app InZ_cons !In_elementsZ_single.
          move => <-.
          tauto.
        } {
          move => y H_y_in.
          by apply H_P2.
        } {
          move => y H_y_in.
          by apply H_P2.
        } {
          rewrite rev_app_distr.
          apply interval_list_invariant_app_intro => //.
          move => x1 x2.
          rewrite !InZ_rev.
          move => H_x1_in /H_P1 [H_x2_in1] H_x2_in2.
          apply H_in_acc_lt => //.
        } {
          apply H_P4.
        }
      }

      move : (H_gr_s1').
      rewrite interval_list_elements_greater_alt2_def => // => H_gr_s1'_alt.

      have : forall (acc : list (Z * N)),
        interval_list_invariant (rev acc) = true ->
        (forall y, InZ y acc <-> (
           y1 <= y < y1 + Z.of_N c1 /\
           y2 <= y < y2 + Z.of_N c2)) ->
        (y1 + Z.of_N c1 <= y2 + Z.of_N c2) ->        
        (inter_aux y2 c2 acc s1' = (acc', s')) ->
        P1 /\ P2 /\ P3 /\ P4. {
        
        intros acc0 H_inv_acc0 H_in_acc0 H_y2c_lt H_inter_aux_eq0.
        have H_in_acc0_lt : (forall x1 x2 : Z,
          InZ x1 acc0 ->
          InZ x2 s1' ->
          List.In x2 (elementsZ_single y2 c2) ->
          Z.succ x1 < x2). {

          intros x1 x2 H_x1_in_acc0 H_x2_in_s1' H_x2_in_yc2.

          suff H_yc1_lt_x2 : Z.succ x1 <= y1 + Z.of_N c1. {
            apply Z.le_lt_trans with (m := y1 + Z.of_N c1) => //.
            by apply H_gr_s1'_alt.
          }
          move : (H_x1_in_acc0).
          rewrite H_in_acc0 Z.le_succ_l.
          tauto.
        }          
        
        move : (IH acc0 H_inv_acc0 H_inv_s1' H_in_acc0_lt H_c2_neq_0).
        rewrite H_inter_aux_eq0.
        move => [H1] [H2] [H3] [H4] H5.
        split; last split => //. {
          move => y.
          rewrite (H1 y).
          rewrite InZ_cons !In_elementsZ_single
                  H_in_acc0.
          tauto.
        } {
          move => y.
          split. {
            move => /H2.
            rewrite InZ_cons.
            by right.
          } {
            rewrite InZ_cons In_elementsZ_single.
            move => []. {
              move => [_] H_y_lt H_lt_y.
              exfalso.
              suff : (y < y) by apply Z.lt_irrefl.
              apply Z.lt_le_trans with (m := y1 + Z.of_N c1) => //.
              apply Z.le_trans with (m := y2 + Z.of_N c2) => //.

              by apply Z.lt_le_incl.
            } {
              apply H3.
            }
          }
        } 
      }
      move => {IH} IH.
         
      clear H_inv_acc H_in_acc_lt acc.
      move : (interval_compare_elim y1 c1 y2 c2) H_inter_aux_eq.
      unfold inter_aux.
      case_eq (interval_compare (y1, c1) (y2, c2)) => H_comp;
         fold inter_aux. {
        move => H_lt_y2.
        apply IH. {
          done.
        } {
          move => x.
          rewrite InZ_nil.
          split => //.
          omega.
        } {
          apply Z.le_trans with (m := y2). {
            by apply Z.lt_le_incl.
          } {
            apply Z_le_add_r.
          }
        }          
      } {
        move => H_eq_y2. 
        apply IH. {
          done.
        } {
          move => x.
          rewrite InZ_nil.
          split => //.
          omega.
        } {
          rewrite H_eq_y2.
          apply Z_le_add_r.
        }          
      } {
        move => [H_y1_lt_y2] [H_y2_lt_yc1] H_yc1_lt_yc2.
        apply IH. {
          rewrite interval_list_invariant_sing.
          by apply Z_to_N_minus_neq_0.
        } {
          move => x.
          rewrite InZ_cons InZ_nil In_elementsZ_single Z2N.id; last omega.
          replace (y1 + (y2 - y1)) with y2 by omega.
          split; omega.
        } {
          by apply Z.lt_le_incl.
        }
      } {
        rewrite /P1 /P2 /P3 /P4.
        move => [H_y2_lt] [H_y1_lt] H_yc1_lt.
        move => [] H_acc' H_s'.
        clear IH P1 P2 P3 P4 H_comp.
        subst s' acc'.
        split; last split; last split. {          
          move => y.
          have H_yc2_intro : y1 + Z.of_N (Z.to_N (y2 + Z.of_N c2 - y1)) =
                             y2 + Z.of_N c2. {
            rewrite Z2N.id; omega.
          }       
          
          rewrite !InZ_cons !In_elementsZ_single InZ_nil H_yc2_intro.
          split. {
            move => [] //.
            move => [H_y1_le] H_y_lt.
            split; last by omega.
            left. omega.
          } {
            move => [H_in_s] [H_y2_le] H_y_lt.
            left.
            split; last assumption.
            move : H_in_s => []. {
              tauto.
            } {              
              move => /H_gr_s1'_alt H_lt_y.
              apply Z.le_trans with (m := y1 + Z.of_N c1). {
                by apply Z_le_add_r.
              } {
                by apply Z.lt_le_incl.
              }
            }
          }
        } {
          move => y.
          split; done.
        } {
          rewrite interval_list_invariant_sing.
          by apply Z_to_N_minus_neq_0.
        } {
          by rewrite interval_list_invariant_cons.
        }
      } {
        rewrite /P1 /P2 /P3 /P4.
        move => [H_y12_eq] H_c12_eq [] H_acc' H_s'.
        clear IH P1 P2 P3 P4 H_comp.
        subst.
        split; last split; last split. {
          move => y.
          rewrite !InZ_cons InZ_nil In_elementsZ_single.
          split; last by tauto. {         
            move => [] //.
            tauto.
          }
        } {
          move => y.
          rewrite InZ_cons In_elementsZ_single.
          split; first by right.
          move => [] //.
          move => [_] H_y_lt H_lt_y.
          exfalso.
          suff : (y2 + Z.of_N c2 < y2 + Z.of_N c2) by
              apply Z.lt_irrefl.
          apply Z.lt_trans with (m := y) => //.
        } {
          rewrite interval_list_invariant_sing //.          
        } {
          assumption.
        }        
      } {
        move => [H_y2_le_y1] [H_yc1_le_yc2] _.
        apply IH. {
          by rewrite interval_list_invariant_sing.
        } {
          move => y.
          rewrite InZ_cons InZ_nil In_elementsZ_single.
          split. {
            move => [] //.
            move => [H_y1_le] H_y_lt.
            split; first done.
            split; omega.
          } {
            move => [?] _.
            by left.
          }
        } {
          assumption.
        }          
      } {
        rewrite /P1 /P2 /P3 /P4.
        move => [H_y1_le] [H_yc2_le] _.
        move => [] H_acc' H_s'.
        clear IH P1 P2 P3 P4 H_comp.
        subst.
        split; last split; last split. {          
          move => y.
          rewrite !InZ_cons !In_elementsZ_single InZ_nil.
          split. {
            move => [] //.
            move => [H_y2_le] H_y_lt.
            split; last by omega.
            left. omega.
          } {
            move => [H_in_s] [H_y2_le] H_y_lt.
            by left.
          }
        } {
          tauto.
        } {
          by rewrite interval_list_invariant_sing.
        } {
          by rewrite interval_list_invariant_cons.
        }
      } {
        rewrite /P1 /P2 /P3 /P4.
        move => H_yc2_lt [] H_acc' H_s'.
        clear IH P1 P2 P3 P4 H_comp.
        subst.
        split; last split; last split. {
          move => y.
          rewrite InZ_cons !In_elementsZ_single InZ_nil.
          split; first done.
          move => [] []. {
            move => [H_y1_le_y] H_y_lt_yc1.
            move => [H_y2_le_y] H_y_lt_yc2.
            omega.
          } {
            move => /H_gr_s1'_alt H_lt_y [_] H_y_lt.
            suff : (y1 + Z.of_N c1 < y1). {
              apply Z.nlt_ge.
              apply Z_le_add_r.
            }
            omega.
          }
        } {
          tauto.
        } {
          done.
        } {
          by rewrite interval_list_invariant_cons.
        }         
      } {
        rewrite /P1 /P2 /P3 /P4.
        move => H_y1_eq [] H_acc' H_s'.
        clear IH P1 P2 P3 P4 H_comp.
        subst acc' s'.
        split; last split; last split. {
          move => y.
          rewrite InZ_cons !In_elementsZ_single InZ_nil.
          split; first done.
          move => [] []. {
            move => [H_y1_le_y] H_y_lt_yc1.
            move => [H_y2_le_y] H_y_lt_yc2.
            omega.
          } {
            move => /H_gr_s1'_alt H_lt_y [_] H_y_lt.
            suff : (y1 + Z.of_N c1 < y1). {
              apply Z.nlt_ge.
              apply Z_le_add_r.
            }
            omega.
          }
        } {
          tauto.
        } {
          done.
        } {
          by rewrite interval_list_invariant_cons.
        }
      }
    }
  Qed.

  Lemma inter_aux2_props :
   forall (s2 s1 acc : t),
    interval_list_invariant (rev acc) = true ->
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    (forall x1 x2, InZ x1 acc -> InZ x2 s1 -> InZ x2 s2 -> Z.succ x1 < x2) ->
    ((forall y, (InZ y (inter_aux2 acc s1 s2) <->
               (InZ y acc) \/ ((InZ y s1) /\ InZ y s2))) /\
    (interval_list_invariant (inter_aux2 acc s1 s2) = true)).
  Proof.
    induction s2 as [| [y2 c2] s2' IH]. {
      move => s1 acc.
      move => H_inv_acc _ _ _.
      unfold inter_aux2.
      replace (match s1 with
        | nil => rev' acc
        | _ :: _ => rev' acc
               end) with (rev' acc); last by case s1.
      rewrite /rev' rev_append_rev app_nil_r.
      split; last done.
      move => y.
      rewrite InZ_nil InZ_rev.
      tauto.
    } {
      intros s1 acc H_inv_acc H_inv_s1.
      rewrite interval_list_invariant_cons.
      move => [H_gr_s2'] [H_c2_neq_0] H_inv_s2'.
      move => H_acc_s12.

      move : H_gr_s2'.
      rewrite interval_list_elements_greater_alt2_def //.
      move => H_gr_s2'.
      
      rewrite /inter_aux2; fold inter_aux2.
      case_eq s1. {
        move => H_s1_eq.
        split. {
          move => y.
          rewrite /rev' rev_append_rev app_nil_r InZ_nil
                  InZ_rev.
          tauto.
        } {
          rewrite /rev' rev_append_rev app_nil_r //.
        }
      } {
        move => [_ _] _ <-.
        case_eq (inter_aux y2 c2 acc s1).
        move => acc' s1' H_inter_aux_eq.

        have H_acc_s1_yc2 : forall x1 x2 : Z,
          InZ x1 acc ->
          InZ x2 s1 ->
          List.In x2 (elementsZ_single y2 c2) ->
          Z.succ x1 < x2. {
          intros x1 x2 H_x1_in H_x2_in1 H_x2_in2.
          apply H_acc_s12 => //.
          rewrite InZ_cons; by left.
        }

        move : (inter_aux_props y2 c2 s1 acc H_inv_acc H_inv_s1 H_acc_s1_yc2 H_c2_neq_0).
        rewrite H_inter_aux_eq.
        move => [H_in_acc'] [H_in_s1'_elim] [H_in_s1'_intro]
                [H_inv_acc'] H_inv_s1'.

        have H_in_acc'_s2' : forall x1 x2 : Z,
            InZ x1 acc' -> InZ x2 s1' -> InZ x2 s2' -> Z.succ x1 < x2. {
          move => x1 x2 /H_in_acc'.
          move => []. {
            move => H_in_acc H_in_s1' H_in_s2'.
            apply H_acc_s12 => //. {
              by apply H_in_s1'_elim.
            } {
              rewrite InZ_cons; by right.
            }
          } {
            rewrite In_elementsZ_single.
            move => [H_in_s1] [_] H_x1_lt _.
            move => /H_gr_s2' H_lt_x2.
            apply Z.le_lt_trans with (m := y2 + Z.of_N c2) => //.
            by apply Z.le_succ_l.
          }
        }
       
        move : (IH s1' acc' H_inv_acc' H_inv_s1' H_inv_s2' H_in_acc'_s2').
        move => [H_inZ_res] H_inv_res.
        split; last assumption.
        move => y.
        rewrite H_inZ_res H_in_acc' InZ_cons
                In_elementsZ_single.
        split. {
          move => []; first by tauto.
          move => [H_y_in_s1' H_y_in_s2'].
          right.
          split; last by right.
          by apply H_in_s1'_elim.
        } {
          move => []. {
            move => H_y_in_acc.
            by left; left.
          } {
            move => [H_y_in_s1].
            move => []. {
              move => H_in_yc2.
              by left; right.
            } {
              right.
              split; last assumption.
              apply H_in_s1'_intro => //.
              by apply H_gr_s2'.
            }
          }
        }
      }
    }
  Qed.
 
  Lemma inter_InZ :
   forall (s1 s2 : t),
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    forall y, (InZ y (inter s1 s2) <-> InZ y s1 /\ InZ y s2).
  Proof.
    intros s1 s2 H_inv_s1 H_inv_s2 y.
    rewrite /inter.

    move : (inter_aux2_props s2 s1 nil).
    move => [] //.
    move => H_in_inter _.
    rewrite H_in_inter InZ_nil.
    tauto.
  Qed.

  Lemma inter_invariant :
   forall (s1 s2 : t),
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    interval_list_invariant (inter s1 s2) = true.
  Proof.
    intros s1 s2 H_inv_s1 H_inv_s2.
    rewrite /inter.

    move : (inter_aux2_props s2 s1 nil).
    move => [] //.
  Qed.
  
 
  Global Instance inter_ok s1 s2 : forall `(Ok s1, Ok s2), Ok (inter s1 s2).
  Proof.
    move => H_ok_s1 H_ok_s2.
    move : (H_ok_s1) (H_ok_s2).
    rewrite /Ok /IsOk /is_encoded_elems_list /add.
    move => [H_inv_s1] H_pre1.
    move => [H_inv_s2] H_pre2.
    split. {
      apply inter_invariant => //.
    } {
      intros y.
      move : (inter_InZ s1 s2 H_inv_s1 H_inv_s2).    
      rewrite /InZ => ->.      
      move => [].
      move => /H_pre1 //.
    }
  Qed.

  Lemma inter_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (inter s s') <-> In x s /\ In x s'.
  Proof.
    intros s s' x H_ok H_ok'.
    rewrite !In_InZ.
    rewrite inter_InZ => //. {
      apply H_ok.
    } {
      apply H_ok'.
    }
  Qed.

  
  (** *** diff specification *)
 
  Lemma diff_aux_alt_def :
    forall (y2 : Z) (c2 : N) (s : t) acc,
      diff_aux y2 c2 acc s = match diff_aux y2 c2 nil s with
                               (acc', s') => (acc' ++ acc, s')
                             end.
  Proof.
    intros y2 c2.
    induction s as [| [y1 c1] acc' IH] => acc. {
      rewrite /diff_aux app_nil_l //.
    } {
      simpl.
      case_eq (diff_aux y2 c2 nil acc') => acc'' s'' H_eq.
      case (interval_compare (y1, c1) (y2, c2));
        rewrite ?(IH ((y1, c1)::acc)) ?(IH ((y1, c1)::nil))
                ?(IH acc) ?(IH ((y1, Z.to_N (y2 - y1)) :: acc))
                ?(IH ((y1, Z.to_N (y2 - y1)) :: nil)) ?H_eq;
        rewrite ?insert_intervalZ_guarded_app -?app_assoc -?app_comm_cons //.
    }
  Qed.

  
  Lemma diff_aux_props :
    forall (y2 : Z) (c2 : N) (s : t) acc,
      interval_list_invariant (List.rev acc) = true ->
      interval_list_invariant s = true ->
      (forall x1 x2, InZ x1 acc -> InZ x2 s -> Z.succ x1 < x2) ->
      (forall x, InZ x acc -> x < y2) ->
      (c2 <> 0%N) ->
      match (diff_aux y2 c2 acc s) with
        (acc', s') => (forall y, InZ y (List.rev_append acc' s') <->
                                 InZ y (List.rev_append acc s) /\ ~(List.In y (elementsZ_single y2 c2))) /\
                      (interval_list_invariant (List.rev_append acc' s') = true) /\
                      (forall x, InZ x acc' -> x < y2 + Z.of_N c2)
      end.
  Proof.
    intros y2 c2.     
    induction s as [| [y1 c1] s1' IH] => acc. {
      rewrite /diff_aux -rev_alt.       
      move => H_inv_acc _ _ H_in_acc H_c2_neq.
      split; last split. {
        move => y; split; last by move => [] //.
        rewrite InZ_rev.         
        move => H_in. split => //.
        move => /In_elementsZ_single => [] [] /Z.nlt_ge H_neq.
        contradict H_neq.
        by apply H_in_acc.
      } {
        assumption.
      } {
        intros x H_in_acc'.
        apply Z.lt_le_trans with (m := y2). {
          by apply H_in_acc.
        } {
          by apply Z_le_add_r.
        }
      }
    } {
      rewrite interval_list_invariant_cons.       
      move => H_inv_acc [H_gr_s1'] [H_c1_neq_0] H_inv_s1'.
      move => H_in_s1 H_in_acc H_c2_neq_0.
       
      rewrite diff_aux_alt_def.
      case_eq (diff_aux y2 c2 nil ((y1, c1) :: s1')).
      move => acc' s' H_diff_aux_eq.

      set P1 := forall y : Z,
        (InZ y acc' \/ InZ y s') <->
        InZ y ((y1, c1) :: s1') /\ ~ List.In y (elementsZ_single y2 c2).
      set P2 := interval_list_invariant (rev acc' ++ s') = true.
      set P3 := forall x : Z, InZ x acc' -> (x < y2 + Z.of_N c2).

      suff : (P1 /\ P2 /\ P3). {
        move => [H_P1] [H_P2] H_P3.
        split; last split. {
          move => y.
          move : (H_P1 y).
          rewrite !rev_append_rev rev_app_distr !InZ_app
                  !InZ_rev In_elementsZ_single.
          suff : (InZ y acc -> ~ y2 <= y < y2 + Z.of_N c2). {
            tauto.
          }
          move => /H_in_acc H_y_lt [H_y_ge] _.
          contradict H_y_ge.
          by apply Zlt_not_le.
        } {
          rewrite rev_append_rev rev_app_distr -app_assoc.
          apply interval_list_invariant_app_intro => //.
          move => x1 x2.
          rewrite InZ_app !InZ_rev.
          move => H_in_acc' H_x2_in_s'.
          suff : (InZ x2 ((y1, c1)::s1')). {
            by apply H_in_s1.
          }
          move : (H_P1 x2).
          tauto.
        } {
          move => x.
          rewrite InZ_app.
          move => []. {
            apply H_P3.
          } {
            move => /H_in_acc H_x_lt.
            eapply Z.lt_trans; eauto.
            by apply Z_lt_add_r.
          }
        }
      }

      move : (H_gr_s1').
      rewrite interval_list_elements_greater_alt2_def => // => H_gr_s1'_alt.

      have : forall (acc : list (Z * N)),
        interval_list_invariant (rev acc) = true ->
        (forall x : Z,
            InZ x acc <->
            ((y1 <= x < y1 + Z.of_N c1) /\ (x < y2))) ->
        (y1 + Z.of_N c1 <= y2 + Z.of_N c2) ->
        (diff_aux y2 c2 acc s1' = (acc', s')) ->
        P1 /\ P2 /\ P3. {
        
        intros acc0 H_inv_acc0 H_in_acc0 H_c1_before H_diff_aux_eq0.
        have H_in_s1' : (forall x1 x2 : Z,
                            InZ x1 acc0 -> InZ x2 s1' -> Z.succ x1 < x2). {
          intros x1 x2 H_x1_in_acc0.
          move => /H_gr_s1'_alt.

          eapply Z.le_lt_trans.
          move : H_x1_in_acc0.
          rewrite Z.le_succ_l H_in_acc0.
          tauto.
        }
        have H_in_acc0' : (forall x : Z, InZ x acc0 -> x < y2). {
          move => x.
          rewrite H_in_acc0.
          move => [_] //.
        }
        move : (IH acc0 H_inv_acc0 H_inv_s1' H_in_s1' H_in_acc0' H_c2_neq_0).
        rewrite H_diff_aux_eq0 !rev_append_rev.
        move => [H1] [H2] H3.
        split; last split => //. {
          move => y.
          move : (H1 y).
          rewrite !InZ_app !InZ_rev In_elementsZ_single.
          move => ->.
          rewrite InZ_cons In_elementsZ_single.
          split. {
            rewrite H_in_acc0 -(Z.nle_gt y2 y).
            tauto.
          } {
            rewrite H_in_acc0 -(Z.nle_gt y2 y).
            move => [] H_in H_nin_i2.
            split; last by assumption.
            move : H_in => [] H_in; last by right.
            left.
            omega.
          }
        }
      }
      move => {IH} IH.
       
      clear H_inv_acc H_in_s1 H_in_acc acc.
      move : (interval_compare_elim y1 c1 y2 c2) H_diff_aux_eq.
      unfold diff_aux.
      case_eq (interval_compare (y1, c1) (y2, c2)) => H_comp;
                                                        fold diff_aux. {
        move => H_lt_y2.
        apply IH. {
          by rewrite interval_list_invariant_sing.
        } {
          move => x.
          rewrite InZ_cons In_elementsZ_single.
          split; last by tauto.
          move => []; last done.
          move => [H_y1_le H_x_lt].         
          split; first done.       
          eapply Z.lt_trans; eauto.
        } {
          apply Z.le_trans with (m := y2). 
            - by apply Z.lt_le_incl.
            - by apply Z_le_add_r.
        }
      } {
        move => H_eq_y2. 
        apply IH. {
          by rewrite interval_list_invariant_sing.
        } {
          move => x.
          rewrite InZ_cons In_elementsZ_single -H_eq_y2.
          split; last by tauto.
          move => []; last done.
          move => []. done.
        } {
          rewrite H_eq_y2.
          by apply Z_le_add_r.
        }
      } {
        move => [H_y1_lt_y2] [H_y2_lt_yc1] H_yc1_lt_yc2.
        apply IH. {
          rewrite interval_list_invariant_sing.
          by apply Z_to_N_minus_neq_0.
        } {
          move => x.
          rewrite InZ_cons In_elementsZ_single Z2N.id; last omega.
          replace (y1 + (y2 - y1)) with y2 by omega.
          split; last tauto.
          move => [] //.
          move => [H_y1_le] H_x_lt.
          repeat split => //.
          apply Z.lt_trans with (m := y2) => //.
        } {
          by apply Z.lt_le_incl.
        }
      } {
        rewrite /P1 /P2 /P3.
        move => [H_y2_lt] [H_y1_lt] H_yc1_lt [H_acc'] H_s'.
        clear IH P1 P2 P3 H_comp.
        subst.
        have H_yc1_intro : y2 + Z.of_N c2 + Z.of_N (Z.to_N (y1 + Z.of_N c1 - (y2 + Z.of_N c2))) = y1 + Z.of_N c1. {
          rewrite Z2N.id; omega.
        }
        have H_nin_yc2 : forall y,
            InZ y s1' -> ~ y2 <= y < y2 + Z.of_N c2. {
          move => y /H_gr_s1'_alt H_lt_y.
          move => [H_y2_le_y].
          apply Z.le_ngt, Z.lt_le_incl.           
          by apply Z.lt_trans with (m := y1 + Z.of_N c1).
        }
        split; last split. {
          move => y.
          rewrite !InZ_cons !In_elementsZ_single H_yc1_intro.
          split. {             
            move => [] //.
            move => []. {
              move => [H_le_y] H_y_lt.
              split. {
                left; omega.
              } {
                move => [_].
                by apply Z.nlt_ge.
              }
            } {
              move : (H_nin_yc2 y). tauto.
            }
          } {
            move => [] []; last by right; right.
            move => [H_y_ge] H_y_lt_yc1 H_nin_yc2'.
            right; left. omega.
          }
        } {
          rewrite interval_list_invariant_cons H_yc1_intro.
          split => //.
          split => //.
          by apply Z_to_N_minus_neq_0.
        } {
          move => [] //.
        }
      } {
        rewrite /P1 /P2 /P3.
        move => [H_y12_eq] H_c12_eq [] H_acc' H_s'.
        clear IH P1 P2 P3 H_comp.
        subst.
        split; last split. {
          move => y.
          rewrite InZ_cons In_elementsZ_single.
          split; last by tauto. {         
            move => [] //.
            move => H_y_in.
            split; first by right.
            move => [] _.
            by apply Z.nlt_ge, Z.lt_le_incl, H_gr_s1'_alt.
          }
        } {
          apply H_inv_s1'.
        } {
          move => x [] //.
        }
      } {
        move => [H_y2_le_y1] [H_yc1_le_yc2] _.
        apply IH. {
          done.
        } {
          move => x.
          split; first done.
          omega.
        } {
          assumption.
        }
      } {
        rewrite /P1 /P2 /P3.
        move => [H_y1_le] [H_yc2_le_yc1] _ [] H_acc' H_s'.
        clear IH P1 P2 P3 H_comp.
        subst.
        have H_yc1_intro : y2 + Z.of_N c2 + Z.of_N (Z.to_N (y1 + Z.of_N c1 - (y2 + Z.of_N c2))) = y1 + Z.of_N c1. {
          rewrite Z2N.id; omega.
        }       
        have H_y1_intro : y1 + Z.of_N (Z.to_N (y2 - y1)) = y2. {
          rewrite Z2N.id; omega.
        }              
        split; last split. {
          move => y.
          rewrite !InZ_insert_intervalZ_guarded
                  !InZ_cons !In_elementsZ_single
                  H_yc1_intro H_y1_intro InZ_nil.
          split. {
            rewrite -!or_assoc.
            move => [[[]|]|] //. {
              move => [H_y1_le_y] H_y_lt.
              split. {
                left.
                split => //.
                apply Z.lt_le_trans with (m := y2 + Z.of_N c2) => //.
                apply Z.lt_trans with (m := y2) => //.
                by apply Z_lt_add_r.
              } {
                move => [] /Z.le_ngt //.
              }
            } {
              move => [H_y2c_le_y] H_y_lt_yc1.
              split. {
                left.
                split => //.
                apply Z.le_trans with (m := y2 + Z.of_N c2) => //.
                apply Z.le_trans with (m := y2) => //.
                apply Z_le_add_r.
              } {
                move => [] _ /Z.lt_nge //.
              }
            } {
              move => H_y_in_s1'.
              split; first by right.
              suff H_suff : y2 + Z.of_N c2 <= y. {
                move => [] _ /Z.lt_nge //.
              }
              apply Z.le_trans with (m := y1 + Z.of_N c1) => //.
              apply Z.lt_le_incl.
              by apply H_gr_s1'_alt.
            }
          } {
            move => [] []; last by tauto.
            move => [H_y1_le_y] H_y_lt H_neq_y2.
            apply not_and in H_neq_y2; last by apply Z.le_decidable.          
            case H_neq_y2. {
              move => /Z.nle_gt H_y_lt'.
              left; left; done.
            } {
              move => /Z.nlt_ge H_le_y.
              right; left; done.               
            }
          }
        } {
          rewrite insert_intervalZ_guarded_rev_nil_app.
          rewrite !interval_list_invariant_insert_intervalZ_guarded => //. {
            rewrite H_yc1_intro => //.
          } {
            rewrite /insert_intervalZ_guarded.
            case_eq ((Z.to_N (y1 + Z.of_N c1 - (y2 + Z.of_N c2)) =? 0)%N). {
              rewrite H_y1_intro.
              move => /N.eqb_eq /N2Z.inj_iff.
              rewrite Z2N.id; last first. {
                by apply Z.le_0_sub.
              }
              move => /Zminus_eq H_yc1_eq.
              eapply interval_list_elements_greater_impl;
                last apply H_gr_s1'.
              rewrite H_yc1_eq.
              apply Z_le_add_r.
            } {
              move => _.
              rewrite interval_list_elements_greater_cons
                      H_y1_intro.
              by apply Z_lt_add_r.
            }
          }
        } {
          move => x.
          rewrite InZ_insert_intervalZ_guarded InZ_cons In_elementsZ_single H_y1_intro InZ_nil.
          move => [] //.
          move => [_] H_x_lt.
          apply Z.lt_le_trans with (m := y2) => //.
          apply Z_le_add_r.
        }
      } {
        rewrite /P1 /P2 /P3.
        move => H_yc2_lt [] H_acc' H_s'.
        clear IH P1 P2 P3 H_comp.
        subst.
        split; last split. {
          move => y.
          rewrite InZ_cons In_elementsZ_single.
          split; last by tauto. {         
            move => [] //.
            move => H_y_in.
            split; first assumption.
            rewrite In_elementsZ_single.
            move => [] H_y2_le H_y_lt.
            case H_y_in; first by omega.
            move => /H_gr_s1'_alt H_lt_y.
            suff : y2 + Z.of_N c2 < y. {
              move => ?. omega.
            }
            apply Z.lt_trans with (m := y1 + Z.of_N c1) => //.
            apply Z.lt_le_trans with (m := y1) => //.
            apply Z_le_add_r.
          }
        } {
          by rewrite interval_list_invariant_cons.
        } {
          done.
        }
      } {
        rewrite /P1 /P2 /P3.
        move => H_yc2_eq [] H_acc' H_s'.
        clear IH P1 P2 P3 H_comp.
        subst.
        split; last split. {
          move => y.
          rewrite InZ_cons In_elementsZ_single.
          split; last by tauto. {         
            move => [] //.
            move => H_y_in.
            split; first assumption.
            rewrite In_elementsZ_single.
            move => [] H_y2_le H_y_lt.
            case H_y_in; first by omega.
            move => /H_gr_s1'_alt H_lt_y.
            suff : y2 + Z.of_N c2 < y. {
              move => ?. omega.
            }
            apply Z.lt_trans with (m := (y2 + Z.of_N c2) + Z.of_N c1) => //. 
            by apply Z_lt_add_r.
          }
        } {
          by rewrite interval_list_invariant_cons.
        } {
          done.
        }
      }
    }
  Qed.


  Lemma diff_aux2_props :
   forall (s2 s1 acc : t),
    interval_list_invariant (rev_append acc s1) = true ->
    interval_list_invariant s2 = true ->
    (forall x1 x2, InZ x1 acc -> InZ x2 s2 -> Z.succ x1 < x2) ->
    ((forall y, (InZ y (diff_aux2 acc s1 s2) <->
               ((InZ y acc) \/ (InZ y s1)) /\ ~InZ y s2)) /\
    (interval_list_invariant (diff_aux2 acc s1 s2) = true)).
  Proof.
    induction s2 as [| [y2 c2] s2' IH]. {
      move => s1 acc H_inv_acc_s1 _ _. 
      rewrite /diff_aux2.
      replace (match s1 with
        | nil => rev_append acc s1
        | _ :: _ => rev_append acc s1
       end) with (rev_append acc s1); last by case s1.
      split. {
        move => y.
        rewrite rev_append_rev InZ_app InZ_rev InZ_nil.
        tauto.
      } {
        assumption.
      }        
    } {
      intros s1 acc H_inv_acc_s1.
      rewrite interval_list_invariant_cons.
      move => [H_gr_s2'] [H_c2_neq_0] H_inv_s2'.
      move => H_acc_s2.
      rewrite /diff_aux2; fold diff_aux2.
      case_eq s1. {
        move => H_s1_eq.
        split. {
          move => y.
          rewrite rev_append_rev InZ_app InZ_nil InZ_rev.
          split; last tauto.
          move => [] // H_y_in.
          split; first by left.
          move => H_y_in'.
          move : (H_acc_s2 _ _ H_y_in H_y_in').
          apply Z.nlt_succ_diag_l.
        } {
          move : H_inv_acc_s1.
           by rewrite H_s1_eq.
        }
      } {
        move => [_ _] _ <-.
        case_eq (diff_aux y2 c2 acc s1).
        move => acc' s1' H_diff_aux_eq.

        have H_acc_lt_y2 : (forall x : Z, InZ x acc -> x < y2). {
          move => x H_x_in.
          have H_y2_in: (InZ y2 ((y2,c2) :: s2')). {
            rewrite InZ_cons.
            left.
            by apply In_elementsZ_single_hd.
          }
          move : (H_acc_s2 _ _ H_x_in H_y2_in).
          apply Z.lt_trans, Z.lt_succ_diag_r.
        }

        have [H_inv_acc [H_inv_s1 H_acc_s1]] :
          interval_list_invariant (rev acc) = true /\
          interval_list_invariant s1 = true /\
          (forall x1 x2 : Z,
             InZ x1 acc -> InZ x2 s1 -> Z.succ x1 < x2). {

          move : H_inv_acc_s1.
          rewrite rev_append_rev.
          move => /interval_list_invariant_app_elim.
          move => [?] [?] H_x.
          split; first assumption.
          split; first assumption.
          move => x1 x2 H_in_x1.
          apply H_x.
          by rewrite InZ_rev.
        }

        move : (diff_aux_props y2 c2 s1 acc H_inv_acc H_inv_s1 H_acc_s1 H_acc_lt_y2 H_c2_neq_0).
        rewrite !H_diff_aux_eq.
        move => [H_inZ_res] [H_inv_res] H_inZ_acc'.

        have H_acc'_s2' : (forall x1 x2 : Z,
                              InZ x1 acc' -> InZ x2 s2' -> Z.succ x1 < x2). {
          move => x1 x2 H_x1_in H_x2_in.
          apply Z.le_lt_trans with (m := y2 + Z.of_N c2). {
            apply Z.le_succ_l.
            by apply H_inZ_acc'.
          } {
            move : H_gr_s2'.
            rewrite interval_list_elements_greater_alt2_def //.
            move => H_gr_s2'.
            by apply H_gr_s2'.
          }
        }

        move : (IH s1' acc' H_inv_res H_inv_s2' H_acc'_s2').
        move => [] H_inZ_diff_res ->.
        split; last done.
        move => y.
        rewrite H_inZ_diff_res.
        move : (H_inZ_res y).
        rewrite !rev_append_rev !InZ_app !InZ_rev InZ_cons.
        move => ->.
        tauto.
      }
    }
  Qed.


  Lemma diff_InZ :
   forall (s1 s2 : t),
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    forall y, (InZ y (diff s1 s2) <-> InZ y s1 /\ ~InZ y s2).
  Proof.
    intros s1 s2 H_inv_s1 H_inv_s2 y.
    rewrite /diff.

    move : (diff_aux2_props s2 s1 nil).
    move => [] //.
    move => H_in_diff _.
    rewrite H_in_diff InZ_nil.
    tauto.
  Qed.

  Lemma diff_invariant :
   forall (s1 s2 : t),
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    interval_list_invariant (diff s1 s2) = true.
  Proof.
    intros s1 s2 H_inv_s1 H_inv_s2.
    rewrite /diff.

    move : (diff_aux2_props s2 s1 nil).
    move => [] //.
  Qed.
  
 
  Global Instance diff_ok s1 s2 : forall `(Ok s1, Ok s2), Ok (diff s1 s2).
  Proof.
    move => H_ok_s1 H_ok_s2.
    move : (H_ok_s1) (H_ok_s2).
    rewrite /Ok /IsOk /is_encoded_elems_list /add.
    move => [H_inv_s1] H_pre1.
    move => [H_inv_s2] H_pre2.
    split. {
      apply diff_invariant => //.
    } {
      intros y.
      move : (diff_InZ s1 s2 H_inv_s1 H_inv_s2).    
      rewrite /InZ => ->.      
      move => [].
      move => /H_pre1 //.
    }
  Qed.

  Lemma diff_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
    intros s s' x H_ok H_ok'.
    rewrite !In_InZ.
    rewrite diff_InZ => //. {
      apply H_ok.
    } {
      apply H_ok'.
    }
  Qed.


  (** *** remove specification *)

  Lemma removeZ_alt_def : forall x s acc,
    interval_list_invariant s = true ->  
    removeZ_aux acc x s = match diff_aux x (1%N) acc s with
                    (acc', s') => rev_append acc' s'
                  end.
  Proof.
    intros y2.
    induction s as [| [y1 c1] s' IH]; first done.

    move => acc.
    rewrite interval_list_invariant_cons /=. 
    move => [H_gr] [H_c1_neq_0] H_inv_s'.
    move : (interval_1_compare_elim y2 y1 c1).
    rewrite interval_1_compare_alt_def.
    rewrite !(interval_compare_swap y1 c1 y2); last first. {
      right. done.
    }
    move : (interval_compare_elim y1 c1 y2 (1%N)).    
    case_eq (interval_compare (y1, c1) (y2, (1%N))) => H_eq. {
      move => H_lt_y2 _.
      have H_yc2_nlt : ~(y2 < y1 + Z.of_N c1). {
        by apply Z.nlt_ge, Z.lt_le_incl.
      }
      have H_y2_nlt : ~(y2 < y1). {
        move => H_y2_y1.
        apply H_yc2_nlt.
        apply Z.lt_le_trans with (m := y1) => //.
        apply Z_le_add_r.
      }
      move : (H_y2_nlt) (H_yc2_nlt) => /Z.ltb_nlt -> /Z.ltb_nlt ->.
      rewrite IH //.
    } {
      move => H_lt_y2 _.
      have H_yc2_nlt : ~(y2 < y1 + Z.of_N c1). {
        apply Z.nlt_ge.
        rewrite H_lt_y2.
        apply Z.le_refl.
      }
      have H_y2_nlt : ~(y2 < y1). {
        move => H_y2_y1.
        apply H_yc2_nlt.
        apply Z.lt_le_trans with (m := y1) => //.
        apply Z_le_add_r.
      }
      move : (H_y2_nlt) (H_yc2_nlt) => /Z.ltb_nlt -> /Z.ltb_nlt ->.
      rewrite IH //.
    } {
      done.
    } {
      done.
    } {
      move => [H_y1_eq] H_c1_eq.
      move => [] // .
      move => [H_lt_y2] H_y2_lt.
      have H_y2_nlt : ~(y2 < y1). {
        apply Z.nlt_ge => //.
      }
      move : (H_y2_nlt) (H_y2_lt) => /Z.ltb_nlt -> /Z.ltb_lt ->.
      rewrite /insert_intervalZ_guarded.

      have -> : (Z.to_N (y1 + Z.of_N c1 - Z.succ y2) =? 0 = true)%N. {
        rewrite H_y1_eq H_c1_eq Z.add_1_r Z.sub_diag //.
      }

      have -> : (Z.to_N (y2 - y1) =? 0 = true)%N. {
        rewrite H_y1_eq Z.sub_diag //.
      }
      done.       
    } {
      move => [H_y2_le] [H_yc1_le] _.
      move => [] //.
      move => [H_y1_le] H_y2_lt.
      have H_y2_nlt : ~(y2 < y1). {
        apply Z.nlt_ge => //.
      }
      move : (H_y2_nlt) (H_y2_lt) => /Z.ltb_nlt -> /Z.ltb_lt ->.

      have H_y1_eq : (y1 = y2) by omega.
      have H_yc1_eq : (y1 + Z.of_N c1 = Z.succ y2). {
        apply Z.le_antisymm. {
          move : H_yc1_le.
          rewrite Z.add_1_r //.
        } {
          by apply Z.le_succ_l.
        }
      }

      rewrite /insert_intervalZ_guarded.
      have -> : (Z.to_N (y1 + Z.of_N c1 - Z.succ y2) =? 0 = true)%N. {
        rewrite H_yc1_eq Z.sub_diag //.
      }

      have -> : (Z.to_N (y2 - y1) =? 0 = true)%N. {
        rewrite H_y1_eq Z.sub_diag //.
      }

      suff -> : diff_aux y2 (1%N) acc s' = (acc, s') by done.

      move : H_gr.
      rewrite H_yc1_eq.
      case s' as [| [y' c'] s'']. {
        done.
      } {
        rewrite interval_list_elements_greater_cons /=
                /interval_compare.
        move => H_lt_y'.
        have -> : y2 + Z.of_N 1 ?= y' = Lt. {
          apply Z.compare_lt_iff.
          by rewrite Z.add_1_r.
        }
        done.
      }
    } { 
      move => [H_y1_le] [H_yc2_le] _.
      move => [] //.
      move => [_] H_y2_lt.
      have H_y2_nlt : ~(y2 < y1). {
        apply Z.nlt_ge => //.
      }
      move : (H_y2_nlt) (H_y2_lt) => /Z.ltb_nlt -> /Z.ltb_lt ->.
      rewrite !rev_append_rev /insert_intervalZ_guarded Z.add_1_r.
      case ((Z.to_N (y2 - y1) =? 0)%N),  (Z.to_N (y1 + Z.of_N c1 - Z.succ y2) =? 0)%N. {
        reflexivity.
      } {
        rewrite /= -!app_assoc //.
      } {
        reflexivity.
      } {
        rewrite /= -!app_assoc //.
      }
    } {
      move => _ H_y2_lt'.
      have H_y2_lt : (y2 < y1). {
        apply Z.lt_trans with (m := Z.succ y2) => //.
        apply Z.lt_succ_diag_r.
      }
      move : (H_y2_lt) => /Z.ltb_lt -> //.
    } {
      move => _ H_y1_eq.
      have H_y2_lt : (y2 < y1). {
        rewrite H_y1_eq.
        apply Z.lt_succ_diag_r.
      }
      move : (H_y2_lt) => /Z.ltb_lt -> //.
    }
  Qed.

  Lemma removeZ_interval_list_invariant : forall s x, interval_list_invariant s = true -> interval_list_invariant (removeZ x s) = true.
  Proof.
    intros s x H_inv.
    rewrite /removeZ removeZ_alt_def //.
    move : (diff_aux_props x (1%N) s nil).
    case_eq (diff_aux x 1%N nil s).
    move => acc' s' H_eq [] //.
    move => _ [] //.
  Qed.

  Lemma removeZ_spec :
   forall (s : t) (x y : Z) (Hs : interval_list_invariant s = true),
    InZ y (removeZ x s) <-> InZ y s /\ ~Z.eq y x.
  Proof.
    intros s x y H_inv.
    rewrite /removeZ removeZ_alt_def //.
    move : (diff_aux_props x (1%N) s nil).
    case_eq (diff_aux x 1%N nil s).
    move => acc' s' H_eq [] //.
    move => -> _.
    rewrite rev_append_rev InZ_app InZ_rev InZ_nil
            In_elementsZ_single1.
    split; move => [H1 H2]; split => //;
      move => H3; apply H2; by rewrite H3.
  Qed.

  Global Instance remove_ok s x : forall `(Ok s), Ok (remove x s).
  Proof.
    rewrite /Ok /interval_list_invariant /remove.
    move => [H_is_ok_s H_enc_s].
    split. {
      by apply removeZ_interval_list_invariant.
    } {
      rewrite /is_encoded_elems_list => y.
      move : (removeZ_spec s (Enc.encode x) y H_is_ok_s).
      rewrite /InZ => -> [] H_y_in _.
      apply H_enc_s => //.
    }
  Qed.

  Lemma remove_spec :
   forall (s : t) (x y : elt) (Hs : Ok s),
    In y (remove x s) <-> In y s /\ ~Enc.E.eq y x.
  Proof.
    intros s x y Hs.
    have H_rs := (remove_ok s x Hs).
    rewrite /remove !In_InZ.
    rewrite removeZ_spec. {
      rewrite Enc.encode_eq //.
    } {
      apply Hs.
    }
  Qed.
  

  (** *** remove_list specification *)

  Lemma remove_list_ok : forall l s, Ok s -> Ok (remove_list l s).
  Proof.
    induction l as [| x l' IH]. {
      done.
    } {
      move => s H_s_ok /=.
      apply IH.
      by apply remove_ok.
    }
  Qed.

  Lemma remove_list_spec : forall x l s, Ok s -> 
     (In x (remove_list l s) <-> ~(InA Enc.E.eq x l) /\ In x s).
  Proof.
    move => x.
    induction l as [| y l' IH]. {
      intros s H.
      rewrite /= InA_nil.
      tauto.
    } {
      move => s H_ok /=.
      rewrite IH remove_spec InA_cons.
      tauto.
    }
  Qed.

  
  (** *** subset specification *)
 
  Lemma subset_flatten_alt_def : forall (s1 s2 : t), 
    subset s1 s2 =
    match (s1, s2) with
    | (nil, _) => true
    | (_ :: _, nil) => false
    | ((y1, c1) :: l1, (y2, c2) :: l2) =>
        match (interval_compare (y1, c1) (y2,c2)) with
          | ICR_before       => false
          | ICR_before_touch => false
          | ICR_after        => subset s1 l2 
          | ICR_after_touch  => false
          | ICR_overlap_before => false
          | ICR_overlap_after => false
          | ICR_equal => subset l1 l2
          | ICR_subsume_1 => subset l1 s2
          | ICR_subsume_2 => false
        end
    end.
  Proof.
    intros s1 s2.    
    case s1, s2 => //. 
  Qed.

  Lemma subset_props_aux : forall y1 c1 l1 y2 c2 l2,
    (exists y, InZ y ((y1, c1) :: l1) /\ ~InZ y ((y2, c2) :: l2)) ->
    (false = true <->
    (forall y : Z,
        InZ y ((y1, c1) :: l1) -> InZ y ((y2, c2) :: l2))).
  Proof.
    intros y1 c1 l1 y2 c2 l2.
    move => [y] [H_y_in H_y_nin].
    split; first done.
    move => H.
    contradict H_y_nin.
    by apply H.
  Qed.
      
  Lemma subset_props_aux_before : forall y1 c1 l1 y2 c2 l2,
    (c1 <> 0%N) ->
    interval_list_invariant ((y2, c2) :: l2) = true ->
    (y1 < y2) ->
    (false = true <->
    (forall y : Z,
        InZ y ((y1, c1) :: l1) -> InZ y ((y2, c2) :: l2))).
  Proof.
    intros y1 c1 l1 y2 c2 l2.
    rewrite interval_list_invariant_cons.
    move => H_c1_neq_0 [H_gr] [H_inv_l2] H_c2_neq_0 H_y1_lt.
    apply subset_props_aux.
    exists y1.
    split. {
      rewrite InZ_cons.
      left.
      by apply In_elementsZ_single_hd.
    } {
      rewrite InZ_cons.
      suff : ~ (List.In y1 (elementsZ_single y2 c2)) /\ ~ InZ y1 l2 by tauto.
      split. {
        rewrite In_elementsZ_single.
        move => [] /Z.le_ngt //.
      } {
        eapply Nin_elements_greater; eauto.
        apply Z.le_trans with (m := y2). {
          by apply Z.lt_le_incl.
        } {
          apply Z_le_add_r.
        }
      }
    }
  Qed.

  
  Lemma subset_props : forall s1 s2 : t,
    interval_list_invariant s1 = true ->
    interval_list_invariant s2 = true ->
    (subset s1 s2 = true <->
     (forall y, InZ y s1 -> InZ y s2)).
  Proof.
    induction s1 as [| [y1 c1] l1 IH1]. {
      move => s2 _ _.
      rewrite subset_flatten_alt_def.
      split; done.
    } {
      induction s2 as [| [y2 c2] l2 IH2]. {
        rewrite interval_list_invariant_cons
                subset_flatten_alt_def.
        move => [_] [H_c1_neq_0] _ _.        
        split => //.
        move => H; move : (H y1).
        rewrite InZ_nil => {H} H.
        contradict H.
        rewrite InZ_cons; left.
        by apply In_elementsZ_single_hd.
      } {
        move => H_inv_s1 H_inv_s2.
        move : (H_inv_s1) (H_inv_s2).
        rewrite !interval_list_invariant_cons.
        move => [H_gr_l1] [H_c1_neq_0] H_inv_l1.
        move => [H_gr_l2] [H_c2_neq_0] H_inv_l2.
        move : (IH2 H_inv_s1 H_inv_l2) => {IH2} IH2.
        have :  forall s2 : t,
          interval_list_invariant s2 = true ->
          (subset l1 s2 = true <->
          (forall y : Z, InZ y l1 -> InZ y s2)). {
          intros. by apply IH1.
        }
        move => {IH1} IH1.

        have H_yc2_nin : ~ InZ (y2 + Z.of_N c2) ((y2, c2) :: l2). {
          rewrite !InZ_cons !In_elementsZ_single.
          move => []. {
            move => [_] /Z.lt_irrefl //.
          } {
            eapply Nin_elements_greater; eauto.
            apply Z.le_refl.
          }
        }
          
        rewrite subset_flatten_alt_def.
        move : (interval_compare_elim y1 c1 y2 c2).
        case (interval_compare (y1, c1) (y2, c2)). {
          move => H_lt_y2.
          apply subset_props_aux_before => //.
          apply Z.le_lt_trans with (m := y1 + Z.of_N c1) => //.
          apply Z_le_add_r.          
        } {
          move => H_y2_eq.
          apply subset_props_aux_before => //.
          rewrite -H_y2_eq.
          by apply Z_lt_add_r.
        } {
          move => [H_y1_lt] _.
          apply subset_props_aux_before => //.
        } {
          move => [H_y2_lt] [H_y1_lt] H_yc2_lt.          
          apply subset_props_aux.
          exists (y2 + Z.of_N c2).
          split => //.
          rewrite !InZ_cons !In_elementsZ_single.
          left.
          split => //.
          by apply Z.lt_le_incl.
        } {
          move => [H_y1_eq] H_c1_eq; subst.
          rewrite IH1 => //.
          split; move => H_pre y; move : (H_pre y) => {H_pre};
            rewrite !InZ_cons. {
            tauto.
          } {
            move => H_pre H_y_in_l1.
            suff : ~(List.In y (elementsZ_single y2 c2)). {
              tauto.
            }
            move : H_gr_l1.
            rewrite interval_list_elements_greater_alt2_def
              // In_elementsZ_single.
            move => H; move : (H y H_y_in_l1) => {H}.
            move => /Z.lt_ngt H_neq [_] //.
          }
        } {
          move => [H_y2_lt_y1] [H_yc1_le] _.
          rewrite IH1.
          split; move => H_pre y; move : (H_pre y) => {H_pre};
            rewrite !InZ_cons. {
            move => H []; last apply H. move => {H}.
            rewrite !In_elementsZ_single.
            move => [H_y1_le] H_y_lt.
            left.
            omega.
          } {
            move => H_pre H_y_in_l1.
            apply H_pre.
            by right.
          } {
            assumption.
          }
        } {
          move => [H_y1_le] [_] []. {
            apply subset_props_aux_before => //.
          } {
            move => H_yc2_lt.
            apply subset_props_aux.
            exists (y2 + Z.of_N c2).
            split => //.
            rewrite !InZ_cons !In_elementsZ_single.
            left.
            split => //.
            apply Z.le_trans with (m := y2) => //.
            apply Z_le_add_r.
          }
        } {
          move => H_yc2_lt_y1.
          rewrite IH2.
          split; move => H_pre y; move : (H_pre y) => {H_pre};
                                                        rewrite !InZ_cons. {
            tauto.
          } {
            rewrite !In_elementsZ_single.
            move => H_pre H_y_in.
            suff : ~(y2 <= y < y2 + Z.of_N c2). {
              tauto.
            }
            move => [H_y2_le H_y_lt].
            move : H_y_in => []. {
              move => [H_y1_le] H_y_lt'.
              omega.
            } {
              eapply Nin_elements_greater; eauto.
              apply Z.le_trans with (m := y1); last first. {
                apply Z_le_add_r.
              }
              apply Z.lt_le_incl.
              apply Z.lt_trans with (m := y2 + Z.of_N c2) => //.
            }
          }
        } {
          move => H_y1_eq.
          apply subset_props_aux.
          exists y1.
          rewrite !InZ_cons.
          split. {
            left.
            by apply In_elementsZ_single_hd.
          } {
            rewrite !In_elementsZ_single H_y1_eq. 
            move => []. {
              move => [_] /Z.lt_irrefl //.
            } {
              eapply Nin_elements_greater; eauto.
              rewrite H_y1_eq.
              apply Z.le_refl.
            }
          }
        }
      }
    }
  Qed. 
     
  Lemma subset_spec :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s'),
   subset s s' = true <-> Subset s s'.
  Proof.
    intros s s' Hs Hs'.
    move : (Hs) (Hs').
    rewrite /Ok /IsOk.
    move => [H_inv_s H_enc_s] [H_inv_s' H_enc_s'].
    rewrite (subset_props s s' H_inv_s H_inv_s').
    rewrite /Subset.
    split. {
      move => H_pre enc_y.
      rewrite !In_InZ.
      apply H_pre.
    } {
      move => H_pre y H_y_in.
      move : (H_enc_s _ H_y_in) => [e] H_e. subst.
      move : (H_pre e) H_y_in.
      rewrite !In_InZ //.
    }
  Qed.
  

  (** *** elements and elementsZ specification *)

  Lemma elements_spec1 : forall (s : t) (x : elt) (Hs : Ok s), List.In x (elements s) <-> In x s.
  Proof.
    intros s x Hs.
    by rewrite In_alt_def.
  Qed.


  Lemma NoDupA_elementsZ_single: forall c x,
    NoDupA Z.eq (elementsZ_single x c).
  Proof.
    induction c as [| c' IH] using N.peano_ind. {
      intros x.
      rewrite elementsZ_single_base //.
    } {
      intros x.
      rewrite elementsZ_single_succ.
      apply NoDupA_app. {
        apply Z.eq_equiv.
      } {
        apply IH.
      } {
        apply NoDupA_singleton.
      } {
        move => y.
        rewrite !InA_alt.
        move => [_] [<-] H_y_in.
        move => [_] [<-] H_y_in'.
        move : H_y_in H_y_in'.
        rewrite In_elementsZ_single /=.
        move => [H_x_le] H_y_lt [] // H_y_eq.
        contradict H_y_lt.
        rewrite H_y_eq.
        apply Z.lt_irrefl.
      }
    }
  Qed.

  Lemma elementsZ_spec2w : forall (s : t) (Hs : Ok s), NoDupA Z.eq (elementsZ s).
  Proof.
    induction s as [| [x c] s' IH]. {
      move => _.
      rewrite elementsZ_nil.
      apply NoDupA_nil.
    } {
      move => H_ok_s.
      move : (H_ok_s) => /Ok_cons [H_interval_list_elements_greater] [H_c] [H_enc] H_s'.
      rewrite elementsZ_cons.
      apply NoDupA_app. {
        apply Z.eq_equiv.
      } {
        by apply IH.
      } {
        apply NoDupA_rev. {
          apply Z.eq_equiv.
        } {
          apply NoDupA_elementsZ_single.
        }
      } {
        move => y.
        rewrite !InA_alt.
        move => [_] [<-] H_y_in.
        move => [_] [<-] H_y_in'.
        move : H_y_in'.
        rewrite -in_rev In_elementsZ_single /=.
        move => [H_x_le] H_y_lt.
        eapply (Nin_elements_greater s' (x + Z.of_N c)) => //. {
          apply H_s'.
        } {
          apply Z.lt_le_incl, H_y_lt.
        } {
          apply H_y_in.
        }
      }
    }
  Qed.

  Lemma elements_spec2w : forall (s : t) (Hs : Ok s), NoDupA Enc.E.eq (elements s).
  Proof.
    intros s Hs.
    rewrite /elements rev_map_alt_def.
    apply NoDupA_rev. {
      apply Enc.E.eq_equiv.
    } {
      eapply NoDupA_map; first by apply elementsZ_spec2w.

      intros x1 x2 H_x1_in H_x2_in H_dec_eq.
      have H_is_enc: is_encoded_elems_list (elementsZ s). {
        apply Hs.
      }
      move : (H_is_enc _ H_x1_in) => [y1 H_x1_eq].
      move : (H_is_enc _ H_x2_in) => [y2 H_x2_eq].
      move : H_dec_eq.
      rewrite -H_x1_eq -H_x2_eq !Enc.decode_encode_ok Enc.encode_eq //.
    }
  Qed.



  (** *** equal specification *)

  Lemma equal_alt_def : forall s1 s2,
    equal s1 s2 = true <-> (s1 = s2).
  Proof.
    induction s1 as [| [x cx] xs IH]. {
      move => [] //.
    } {
      move => [] //=.
      move => [y cy] ys.
      rewrite !andb_true_iff IH N.eqb_eq Z.eqb_eq.
      split. {
        move => [->] [->] -> //.
      } {
        move => [->] -> -> //.
      }
    }
  Qed.


  Lemma equal_elementsZ :
    forall (s s' : t) {Hs : Ok s} {Hs' : Ok s'},
    (forall x, (InZ x s <-> InZ x s')) -> (s = s').
  Proof.
    intros s s'.
    move => H_ok_s H_ok_s' H_InZ_eq.
    have [] : ((subset s s' = true) /\ (subset s' s = true)). {
      rewrite !subset_spec /Subset.
      split => x; rewrite !In_InZ H_InZ_eq //.
    }
    have : interval_list_invariant s' = true by apply H_ok_s'.
    have : interval_list_invariant s = true by apply H_ok_s.
    clear H_ok_s H_ok_s' H_InZ_eq.
    move : s s'.
    induction s as [| [x1 c1] s1 IH];
      case s' as [| [x2 c2] s2] => //.
    rewrite !interval_list_invariant_cons.
    move => [H_gr_s1] [H_c1_neq_0] H_inv_s1.
    move => [H_gr_s2] [H_c2_neq_0] H_inv_s2.
    rewrite subset_flatten_alt_def
            (subset_flatten_alt_def ((x2, c2)::s2)).
    rewrite (interval_compare_swap x1 c1); last by left.
    move : (interval_compare_elim x1 c1 x2 c2).
    case (interval_compare (x1, c1) (x2, c2)) => //.
    move => [->] -> H_sub_s12 H_sub_s21.

    suff -> : s1 = s2 by done.
    by apply IH.
  Qed.
 

  Lemma equal_spec :
    forall (s s' : t) {Hs : Ok s} {Hs' : Ok s'},
    equal s s' = true <-> Equal s s'.
  Proof.
    intros s s' Hs Hs'.
    rewrite equal_alt_def /Equal.
    split. {
      move => -> //.
    } {
      move => H.
      apply equal_elementsZ => // x.
      move : (H (Enc.decode x)).
      rewrite !In_InZ.

      suff H_ex : (forall s'', Ok s'' -> InZ x s'' -> (exists z, Enc.encode z = x)). {
        move => HH.
        split. {
          move => H3.
          move : HH (H3).
          move : (H_ex s Hs H3) => [z] <-.
          rewrite Enc.decode_encode_ok => <- //.
        } {
          move => H3.
          move : HH (H3).
          move : (H_ex s' Hs' H3) => [z] <-.
          rewrite Enc.decode_encode_ok => <- //.
        } 
      }
      clear.
      intros s'' H_ok H_in_x.
      have H_enc : is_encoded_elems_list (elementsZ s''). {
        apply H_ok.
      }
      apply H_enc.
      apply H_in_x.
    }
  Qed.

  (** *** compare *)
  Definition lt (s1 s2 : t) : Prop := (compare s1 s2 = Lt).

  Lemma compare_eq_Eq : forall s1 s2,
    (compare s1 s2 = Eq <-> equal s1 s2 = true).
  Proof.
    induction s1 as [| [y1 c1] s1' IH];
      case s2 as [| [y2 c2] s2'] => //.
    rewrite /= !andb_true_iff -IH Z.eqb_eq N.eqb_eq.
    move : (Z.compare_eq_iff y1 y2).
    case (Z.compare y1 y2). {
      move => H.
      have -> : y1 = y2. by apply H.
      clear H.

      move : (N.compare_eq_iff c1 c2).
      case (N.compare c1 c2). {
        move => H.
        have -> : c1 = c2. by apply H.
        tauto.
      } {
        move => H.
        have H_neq : ~(c1 = c2). by rewrite -H => {H}.
        tauto.
      } {        
        move => H.
        have H_neq : ~(c1 = c2). by rewrite -H => {H}.
        tauto.
      }
    } {
      move => H.
      have H_neq : ~(y1 = y2). by rewrite -H => {H}.
      tauto.
    } {
      move => H.
      have H_neq : ~(y1 = y2). by rewrite -H => {H}.
      tauto.
    }
  Qed.

  Lemma compare_eq_Lt_nil_l : forall s,
    compare nil s = Lt <-> s <> nil.
  Proof.
    intros s.
    case s => //=.
    split => //.
  Qed.

  Lemma compare_eq_Lt_nil_r : forall s,
    ~(compare s nil = Lt).
  Proof.
    intros s.
    case s as [| [y1 c1] s'] => //=.
  Qed.
  
  Lemma compare_eq_Lt_cons : forall y1 y2 c1 c2 s1 s2,
    compare ((y1, c1)::s1) ((y2, c2)::s2) = Lt <->
    (y1 < y2) \/ ((y1 = y2) /\ (c1 < c2)%N) \/
    ((y1 = y2) /\ (c1 = c2) /\ compare s1 s2 = Lt).
  Proof.
    intros y1 y2 c1 c2 s1 s2.
    rewrite /=.
    case_eq (Z.compare y1 y2). {
      move => /Z.compare_eq_iff ->.
      case_eq (N.compare c1 c2). {
        move => /N.compare_eq_iff ->.
        split. {
          move => H.
          right; right.
          done.
        } {
          move => [| []]. {
            move => /Z.lt_irrefl //.
          } {
            move => [_] /N.lt_irrefl //.
          } {
            move => [_] [_] -> //.
          }
        }
      } {
        move => /N.compare_lt_iff H_c1_lt.
        split => //.
        move => _.
        right; left. done.
      } {
        move => /N.compare_gt_iff H_c2_lt.
        split => //.
        move => [| []]. {
          move => /Z.lt_irrefl //.
        } {
          move => [_] /N.lt_asymm //.
        } {
          move => [_] [] H_c1_eq.
          contradict H_c2_lt.
          subst c1.
          by apply N.lt_irrefl.
        }
      }
    } {
      move => /Z.compare_lt_iff.
      tauto.
    } {
      move => /Z.compare_gt_iff H_y2_lt.
      split => //.
      move => [| []]. {
        move => /Z.lt_asymm //.
      } {
        move => [] H_y1_eq.
        exfalso. omega.
      } {
        move => [] H_y1_eq.
        exfalso. omega.
      }
    }
  Qed.
  
  
  Lemma compare_antisym: forall (s1 s2 : t),
    (compare s1 s2) = CompOpp (compare s2 s1).
  Proof.
    induction s1 as [| [y1 c1] s1' IH];
      case s2 as [| [y2 c2] s2'] => //.
    rewrite /= (Z.compare_antisym y1 y2) (N.compare_antisym c1 c2).
    case (Z.compare y1 y2) => //=.
    case (N.compare c1 c2) => //=.
  Qed.


  Lemma compare_spec : forall s1 s2,
    CompSpec eq lt s1 s2 (compare s1 s2).
  Proof.
    intros s1 s2.
    rewrite /CompSpec /lt (compare_antisym s2 s1).
    case_eq (compare s1 s2). {
      rewrite compare_eq_Eq equal_alt_def => ->.
      by apply CompEq.
    } {
      move => _.
      by apply CompLt.
    } {
      move => _.
      by apply CompGt.
    }
  Qed.

  Lemma lt_Irreflexive : Irreflexive lt.
  Proof.
    rewrite /Irreflexive /Reflexive /complement /lt.
    intros x.
    suff -> : compare x x = Eq by done.
    rewrite compare_eq_Eq equal_alt_def //.
  Qed.

  Lemma lt_Transitive : Transitive lt.
  Proof.
    rewrite /Transitive /lt.
    induction x as [| [y1 c1] s1' IH];
      case y as [| [y2 c2] s2'];
      case z as [| [y3 c3] s3'] => //.

    rewrite !compare_eq_Lt_cons.
    move => [H_y1_lt | [[->] H_c1_lt | [->] [->] H_comp]]
            [H_y2_lt | [[<-] H_c2_lt | [<-] [<-] H_comp']]. {
      left.
      by apply Z.lt_trans with (m := y2).
    } {
      by left.
    } {
      by left.
    } {
      by left.
    } {
      right; left.
      split => //.
      by apply N.lt_trans with (m := c2).
    } {
      by right; left.
    } {
      by left.
    } {
      by right; left.
    } {
      right; right.
      split => //.
      split => //.
      by apply (IH s2').
    }
  Qed.
             
  (** *** elements is sorted *)
  
  Lemma elementsZ_single_sorted : forall c x,
    sort Z.lt (elementsZ_single x c).
  Proof.
    induction c as [| c' IH] using N.peano_ind. {
      intro x.
      rewrite elementsZ_single_base.
      apply Sorted_nil.
    } {
      intro x.
      rewrite elementsZ_single_succ_front.
      apply Sorted_cons. {
        apply IH.
      } {
        case (N.zero_or_succ c'). {
          move => ->.
          rewrite elementsZ_single_base //.
        } {
          move => [c''] ->.
          rewrite elementsZ_single_succ_front.
          constructor.
          apply Z.lt_succ_diag_r.
        }
      }
    }
  Qed.

  Lemma elementsZ_sorted : forall s,
    interval_list_invariant s = true ->
    sort Z.lt (rev (elementsZ s)).
  Proof.
    induction s as [| [y c] s' IH]. {
      move => _.
      rewrite elementsZ_nil.
      apply Sorted_nil.
    } {
      rewrite interval_list_invariant_cons elementsZ_cons
              rev_app_distr rev_involutive.
      move => [H_gr] [H_c_neq_0] H_inv_s'.
      apply SortA_app with (eqA := Logic.eq). {
        apply eq_equivalence.
      } {
        apply elementsZ_single_sorted.
      } {
        by apply IH.
      } {
        intros x1 x2.
        move => /InA_alt [_] [<-] /In_elementsZ_single [_ H_x1_lt].
        move => /InA_alt [_] [<-].
        rewrite -In_rev => H_x2_in.

        apply Z.lt_trans with (m := (y + Z.of_N c)) => //.
        eapply interval_list_elements_greater_alt2_def;
          eauto.
      }
    }
  Qed.

  
  Lemma elements_sorted : forall s,
    Ok s ->
    sort Enc.E.lt (elements s).
  Proof.
    move => s [H_inv] H_enc.
    rewrite /elements rev_map_alt_def -map_rev.
    have : (forall x : Z, List.In x (rev (elementsZ s)) ->
           exists e : Enc.E.t, Enc.encode e = x). {
      move => x.
      move : (H_enc x).
      rewrite In_rev //.
    }
    move : (elementsZ_sorted s H_inv) => {H_enc}.
    generalize (rev (elementsZ s)).
    induction l as [| x xs IH]. {
      rewrite /= => _ _.
      apply Sorted_nil.
    } {
      move => H_sort H_enc.
      apply Sorted_inv in H_sort as [H_sort H_hd_rel].
      simpl.
      apply Sorted_cons. {
        apply IH => //.
        move => xx H_xx_in.
        apply H_enc.
        by apply in_cons.
      } {
        move : H_hd_rel H_enc.
        case xs => //=.
        move => x' xs' H_hd_rel H_enc.
        apply HdRel_inv in H_hd_rel.
        apply HdRel_cons.
        rewrite -Enc.encode_lt.
        have [y H_y] : (exists y, Enc.encode y = x). {
          apply H_enc. by left.
        }
        have [y' H_y'] : (exists y', Enc.encode y' = x'). {
          apply H_enc. by right; left.
        }
        move : H_hd_rel.
        rewrite -!H_y -!H_y' !Enc.decode_encode_ok //.
      }
    }
  Qed.   
        
  
  (** *** choose specification *)

  Definition min_eltZ_spec1 :
    forall (s : t) (x : Z),
      interval_list_invariant s = true ->
      min_eltZ s = Some x -> InZ x s. 
  Proof.   
    intros s x.
    case s as [| [x' c] s']. {
      rewrite /min_eltZ //.
    } {
      rewrite /min_eltZ InZ_cons interval_list_invariant_cons.
      move => [_] [H_c_neq] _ [->].
      left.
      by apply In_elementsZ_single_hd.
    }
  Qed.

  Lemma min_eltZ_spec2 :
    forall (s : t) (x y : Z) (Hs : Ok s),
    min_eltZ s = Some x -> InZ y s -> ~ Z.lt y x.
  Proof.
    intros s x y H_ok H_min H_in H_y_lt_x.
    eapply (Nin_elements_greater s (Z.pred x)) => //; last apply H_in. {
      move : H_ok H_min.
      case s => //.
      move => [z c] s' _ [<-].
      rewrite interval_list_elements_greater_cons.
      apply Z.lt_pred_l.
    } {
      apply H_ok.
    } {
      by apply Z.lt_le_pred.
    }
  Qed.

  Definition min_eltZ_spec3 :
    forall (s : t),
      min_eltZ s = None -> forall x, ~InZ x s. 
  Proof.   
    intros s.
    case s as [| [x' c] s'];
      rewrite /min_eltZ //.
    move => _ x //.
  Qed.

  Definition min_elt_spec1 :
    forall (s : t) (x : elt) (Hs : Ok s), min_elt s = Some x -> In x s. 
  Proof.   
    rewrite /min_elt.
    move => s x H_ok.
    case_eq (min_eltZ s) => //.
    move => z H_min_elt [<-].
    apply InZ_In => //.
    apply min_eltZ_spec1 => //.
    apply H_ok.
  Qed.

  Definition min_elt_spec2 :
    forall (s : t) (x y : elt) (Hs : Ok s), min_elt s = Some x -> In y s -> ~(Enc.E.lt y x). 
  Proof.   
    rewrite /min_elt.
    move => s x y H_ok.
    case_eq (min_eltZ s) => //.
    move => z H_min_elt [<-].
    rewrite In_InZ => H_inZ.    
    have H_y_eq : y = Enc.decode (Enc.encode y). {
      by rewrite Enc.decode_encode_ok.
    }
    rewrite H_y_eq -Enc.encode_lt.
    apply (min_eltZ_spec2 _ _ _ H_ok); last first. {
      by rewrite Enc.decode_encode_ok.
    }
    suff -> : Enc.encode (Enc.decode z) = z by assumption.
    apply encode_decode_eq with (s := s) => //.
    apply min_eltZ_spec1 => //.
    apply H_ok.
  Qed.

  Definition min_elt_spec3 :
    forall s : t, min_elt s = None -> Empty s.
  Proof.   
    rewrite /min_elt /min_eltZ /Empty /In.
    case s as [| [x' c] s'] => //.
    move => _ e.
    rewrite elements_nil InA_nil //.
  Qed.


  Definition choose_spec1 :
    forall (s : t) (x : elt) (Hs : Ok s), choose s = Some x -> In x s. 
  Proof.   
    rewrite /choose.
    apply min_elt_spec1.
  Qed.

  Definition choose_spec2 :
    forall s : t, choose s = None -> Empty s.
  Proof.   
    rewrite /choose.
    apply min_elt_spec3.
  Qed.

  Lemma choose_spec3: forall s s' x x', Ok s -> Ok s' ->
    choose s = Some x -> choose s' = Some x' -> Equal s s' -> x = x'.
  Proof.
    intros s s' x x' Hs Hs' Hx Hx'.
    rewrite -equal_spec equal_alt_def => H_s_eq.
    move : Hx Hx'.
    rewrite H_s_eq => -> [] //.
  Qed.

    
  Definition max_eltZ_spec1 :
    forall (s : t) (x : Z),
      interval_list_invariant s = true ->
      max_eltZ s = Some x -> InZ x s. 
  Proof.   
    intros s x.
    induction s as [| [x' c] s' IH]. {
      rewrite /max_eltZ //.
    } {
      rewrite InZ_cons interval_list_invariant_cons /=.
      move => [_] [H_c_neq].
      case s' as [| [y' c'] s'']. {
        move => _ [<-].
        left. {
          rewrite In_elementsZ_single.
          split. {
            rewrite -Z.lt_le_pred.
            by apply Z_lt_add_r.
          } {
            apply Z.lt_pred_l.
          }
        }
      } {
        move => H_inv H_max_eq.
        right.
        by apply IH.
      }
    }
  Qed.

  Lemma max_eltZ_spec2 :
    forall (s : t) (x y : Z),
    interval_list_invariant s = true ->
    max_eltZ s = Some x -> InZ y s -> ~ Z.lt x y.
  Proof.
    induction s as [| [y c] s' IH]. {
      done.
    } {
      move => x x'.
      rewrite interval_list_invariant_cons.
      move => [H_gr] [H_c_neq_0] H_inv_s'.
      have H_gr' : (forall xx : Z, InZ xx (s') -> y + Z.of_N c < xx). {
        apply interval_list_elements_greater_alt2_def => //.
      }

      case s' as [| [y' c'] s'']. {
        move => [<-].
        rewrite InZ_cons InZ_nil In_elementsZ_single.
        omega.
      } {
        move => H_max_eq.
        rewrite InZ_cons.
        move => []; last by apply IH.
        rewrite In_elementsZ_single.
        move => [_] H_x'_lt H_lt_x'.

        have H_x_in : InZ x ((y', c')::s''). {
          by apply max_eltZ_spec1.
        }
        
        move : (H_gr' _ H_x_in).
        apply Z.nlt_ge, Z.lt_le_incl.
        by apply Z.lt_trans with (m := x').
      }
    }
  Qed.

  Lemma max_eltZ_eq_None :
    forall (s : t),
      max_eltZ s = None -> s = nil.
  Proof.
    induction s as [| [x' c] s' IH] => //.
    move : IH.
    case s' as [| [y' c'] s''] => //=.
    move => H H_pre.
    move : (H H_pre) => //.
  Qed.   
    

  Definition max_eltZ_spec3 :
    forall (s : t),
      max_eltZ s = None -> forall x, ~InZ x s. 
  Proof.
    move => s /max_eltZ_eq_None -> x /InZ_nil //.
  Qed.

  Definition max_elt_spec1 :
    forall (s : t) (x : elt) (Hs : Ok s), max_elt s = Some x -> In x s. 
  Proof.   
    rewrite /max_elt.
    move => s x H_ok.
    case_eq (max_eltZ s) => //.
    move => z H_max_elt [<-].
    apply InZ_In => //.
    apply max_eltZ_spec1 => //.
    apply H_ok.
  Qed.

  Definition max_elt_spec2 :
    forall (s : t) (x y : elt) (Hs : Ok s), max_elt s = Some x -> In y s -> ~(Enc.E.lt x y). 
  Proof.   
    rewrite /max_elt.
    move => s x y H_ok.
    move : (H_ok) => [H_inv] _.
    case_eq (max_eltZ s) => //.
    move => z H_max_elt [<-].
    rewrite In_InZ => H_inZ.    
    rewrite -Enc.encode_lt.
    apply (max_eltZ_spec2 _ _ _ H_inv) => //.
    suff -> : Enc.encode (Enc.decode z) = z => //.
    apply encode_decode_eq with (s := s) => //.
    apply max_eltZ_spec1 => //.
  Qed.

  Definition max_elt_spec3 :
    forall s : t, max_elt s = None -> Empty s.
  Proof.
    intro s.
    rewrite /max_elt /Empty.
    case_eq (max_eltZ s) => //.
    move => /max_eltZ_eq_None -> _ x.
    rewrite /In elements_nil InA_nil //.
  Qed.


  (** *** fold specification *)

  Lemma fold_spec :
   forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (flip f) (elements s) i.
  Proof.
    intros s A i f.
    rewrite /fold fold_elementsZ_alt_def /elements
            rev_map_alt_def -map_rev.
    move : i.
    generalize (rev (elementsZ s)).
    induction l as [| x xs IH]. {
      done.
    } {
      move => i.
      rewrite /= IH //.
    }
  Qed.

 
  (** *** cardinal specification *)

  Lemma cardinalN_spec : forall (s : t) (c : N), 
    cardinalN c s = (c + N.of_nat (length (elements s)))%N.
  Proof.
    induction s as [| [x cx] xs IH]. {
      intros c.
      rewrite elements_nil /= N.add_0_r //.
    } {
      intros c.
      rewrite /= IH.
      rewrite /elements !rev_map_alt_def !rev_length !map_length.
      rewrite elementsZ_cons app_length Nat2N.inj_add rev_length.
      rewrite length_elementsZ_single N2Nat.id.
      ring.
    }
  Qed.

  Lemma cardinal_spec :
   forall (s : t),
   cardinal s = length (elements s).
  Proof.
    intros s.
    rewrite /cardinal cardinalN_spec N.add_0_l Nat2N.id //.
  Qed.


  (** *** for_all specification *)

  Lemma for_all_spec :
   forall (s : t) (f : elt -> bool) (Hs : Ok s),
   Proper (Enc.E.eq==>eq) f ->
   (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof.
    intros s f Hs H.
    rewrite /for_all /For_all /In fold_elementsZ_alt_def
            /elements rev_map_alt_def -map_rev.
    generalize (rev (elementsZ s)).
    induction l as [| x xs IH]. {      
      split => // _ x /= /InA_nil //.
    } {
      rewrite /=.
      case_eq (f (Enc.decode x)) => H_f_eq. {
        rewrite IH.
        split. {
          move => HH x' /InA_cons []. {
            by move => ->.
          } {
            apply HH.
          }
        } {
          move => HH x' H_in.
          apply HH.
          apply InA_cons.
          by right.
        }
      } {
        split; move => HH. {
          contradict HH.
          case xs => //.
        } {
          exfalso.
          have H_in: (InA Enc.E.eq (Enc.decode x) (Enc.decode x :: map Enc.decode xs)). {
            apply InA_cons.
            left.
            apply Enc.E.eq_equiv.
          }
          move : (HH _ H_in).
          rewrite H_f_eq => //.
        }
      }
    }
  Qed.

  (** *** exists specification *)

  Lemma exists_spec :
   forall (s : t) (f : elt -> bool) (Hs : Ok s),
   Proper (Enc.E.eq==>eq) f ->
   (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof.
    intros s f Hs H.
    rewrite /exists_ /Exists /In fold_elementsZ_alt_def
            /elements rev_map_alt_def -map_rev.
    generalize (rev (elementsZ s)).
    induction l as [| x xs IH]. {      
      split => //.
      move => [x] /= [] /InA_nil //.
    } {
      rewrite /=.
      case_eq (f (Enc.decode x)) => H_f_eq. {
        split => _. {
          exists (Enc.decode x).
          split => //.
          apply InA_cons.
          left.
          apply Enc.E.eq_equiv.
        } {
          case xs => //.
        }
      } {
        rewrite IH.
        split. {
          move => [x0] [H_in] H_f_x0.
          exists x0.
          split => //.
          apply InA_cons.
          by right.
        } {
          move => [x0] [] /InA_cons H_in H_f_x0.
          exists x0.
          split => //.
          move : H_in => [] // H_in.
          contradict H_f_x0.
          rewrite H_in H_f_eq //.
        }
      }
    }
  Qed.


  (** *** filter specification *)    
    
  Definition partitionZ_aux_invariant (x : Z) acc c :=
    interval_list_invariant (List.rev (partitionZ_fold_skip acc c)) = true /\
    match c with
      None => (forall y', InZ y' acc -> Z.succ y' < x)
    | Some (y, c') => (x = y + Z.of_N c')
    end.

  Lemma partitionZ_aux_invariant_insert : forall x acc c,
    partitionZ_aux_invariant x acc c ->
    partitionZ_aux_invariant (Z.succ x) acc
      (Some (partitionZ_fold_insert c x)).
  Proof.
    intros x acc c.
    rewrite /partitionZ_fold_insert /partitionZ_aux_invariant
            /partitionZ_fold_skip.
    case c; last first. {
      move => [H_inv] H_in.
      rewrite /= interval_list_invariant_app_iff Z.add_1_r.
      split; last done.
      split; first done.
      split; first done.
      move => x1 x2.
      rewrite InZ_rev InZ_cons InZ_nil In_elementsZ_single1.
      move => H_x1_in [] // <-.
      by apply H_in.
    } {
      move => [y c'].
      rewrite /= !interval_list_invariant_app_iff
        N2Z.inj_succ Z.add_succ_r .
      rewrite !interval_list_invariant_cons !interval_list_invariant_nil.
      move => [] [H_inv_acc] [] [] _ [H_c_neq_0] _
        H_in_c ->.      
      split; last done.
      split; first done.
      split. {
        split; first done.
        split; last done.
        apply N.neq_succ_0.
      } {
        move => x1 x2.
        rewrite InZ_cons InZ_nil In_elementsZ_single.
        move => H_x1_in [] // [H_y_le] H_x2_lt.
        apply Z.lt_le_trans with (m := y) => //. 
        apply H_in_c => //.
        rewrite InZ_cons In_elementsZ_single.
        left.
        split. {
          apply Z.le_refl.
        } {
          by apply Z_lt_add_r.
        }
      }
    }
  Qed.

  Lemma partitionZ_aux_invariant_skip : forall x acc c,
    partitionZ_aux_invariant x acc c ->
    partitionZ_aux_invariant (Z.succ x) (partitionZ_fold_skip acc c) None.
  Proof.
    intros x acc c.
    rewrite /partitionZ_fold_skip /partitionZ_aux_invariant
            /partitionZ_fold_skip.
    case c; last first. {
      move => [H_inv] H_in.
      split; first done.
      move => y' H_y'_in.
      apply Z.lt_trans with (m := x). {
        by apply H_in.
      } {
        apply Z.lt_succ_diag_r.
      }
    } {
      move => [y c'] [H_inv] ->.
      split => //.
      move => y'.
      rewrite InZ_cons In_elementsZ_single.
      move => []. {
        move => [_].
        rewrite -Z.succ_lt_mono //.
      } {
        move : H_inv.
        rewrite /= !interval_list_invariant_app_iff interval_list_invariant_cons.
        move => [_] [] [_] [H_c'_neq] _ H_pre H_y'_in.
        apply Z.lt_trans with (m := y). {
          apply H_pre. {
            by rewrite InZ_rev.
          } {
            rewrite InZ_cons.
            left.
            by apply In_elementsZ_single_hd.
          }
        }
        apply Z.lt_succ_r, Z_le_add_r.
      }
    }
  Qed.

  Definition partitionZ_fold_current (c : option (Z * N)) :=
    match c with
       None => nil
     | Some yc => yc::nil
    end.
  
  Lemma InZ_partitionZ_fold_current_Some : forall yc y,
     InZ y (partitionZ_fold_current (Some yc)) <->
     InZ y (yc :: nil).
  Proof. done. Qed.

  Lemma InZ_partitionZ_fold_insert : forall c x y l,
   match c with
   | Some (y, c') => x = y + Z.of_N c'
   | None => True
   end -> (
   InZ y (partitionZ_fold_insert c x :: l) <->
    ((x = y) \/ InZ y (partitionZ_fold_current c) \/
       InZ y l)).
  Proof.
    intros c x y l.
    rewrite /partitionZ_fold_insert /partitionZ_fold_current
            /partitionZ_fold_skip.
    case c. {
      move => [y' c'] ->.
      rewrite !InZ_cons elementsZ_single_succ in_app_iff
              InZ_nil /=.
      tauto.
    } {
      rewrite InZ_cons InZ_nil In_elementsZ_single1.
      tauto.
    }
  Qed.  

  Lemma InZ_partitionZ_fold_skip : forall c acc y,
    InZ y (partitionZ_fold_skip acc c) <->
    (InZ y (partitionZ_fold_current c) \/ InZ y acc).
  Proof.
    intros c acc y.
    rewrite /partitionZ_fold_skip /partitionZ_fold_current
            /partitionZ_fold_skip.
    case c. {
      move => [y' c'].
      rewrite !InZ_cons InZ_nil /=.
      tauto.
    } {
      rewrite InZ_nil.
      tauto.
    }
  Qed.  
  
  Lemma filterZ_single_aux_props :
    forall f c x acc cur,
      partitionZ_aux_invariant x acc cur ->
      match (filterZ_single_aux f (acc, cur) x c) with
        (acc', c') =>
        let r := partitionZ_fold_skip acc' c' in
        interval_list_invariant (List.rev r) = true /\
        (forall y', InZ y' r <-> (InZ y' (partitionZ_fold_skip acc cur) \/
                                    (f y' = true /\ List.In y' (elementsZ_single x c))))

      end.
  Proof.
    intro f.
    induction c as [| c' IH] using N.peano_ind. {
      intros x acc cur.
      rewrite /partitionZ_aux_invariant.
      move => [H_inv] _.
      rewrite /filterZ_single_aux fold_elementsZ_single_zero /=.
      tauto.
    }
    intros x acc cur H_inv.
    have -> :  filterZ_single_aux f (acc, cur) x (N.succ c') =
               filterZ_single_aux f (filterZ_fold_fun f (acc, cur) x) (Z.succ x) c'. {
        by rewrite /filterZ_single_aux fold_elementsZ_single_succ.
    }
    case_eq (filterZ_fold_fun f (acc, cur) x). 
    move => acc' cur' H_fold_eq.

    case_eq (filterZ_single_aux f (acc', cur') (Z.succ x) c').
    move => acc'' cur'' H_succ_eq.

    have H_inv' : partitionZ_aux_invariant (Z.succ x) acc' cur'. {
      move : H_fold_eq H_inv.
      rewrite /filterZ_fold_fun.
      case (f x); move => [<-] <-. {
        apply partitionZ_aux_invariant_insert.
      } {
        apply partitionZ_aux_invariant_skip.
      }
    }
   
    move : (IH (Z.succ x) acc' cur' H_inv') => {IH}.
    rewrite H_succ_eq /=.
    set r := partitionZ_fold_skip acc'' cur''.
    move => [H_inv_r] H_in_r.
    split; first assumption.

    move => y'.
    move : H_fold_eq.
    rewrite H_in_r /filterZ_fold_fun.
    case_eq (f x) => H_fx [<-] <-. {
      rewrite InZ_partitionZ_fold_skip InZ_partitionZ_fold_current_Some InZ_partitionZ_fold_skip elementsZ_single_succ_front.
      rewrite InZ_partitionZ_fold_insert; last first. {
        move : H_inv.
        rewrite /partitionZ_aux_invariant => [[_]].
        case cur => //.
      }
      rewrite InZ_nil /=.
      split; last by tauto.
      move => []; last by tauto.
      move => []; last by tauto.
      move => []. {
        move => <-.
        tauto.
      } {
        tauto.
      }
    } {
      rewrite InZ_partitionZ_fold_skip /partitionZ_fold_current InZ_partitionZ_fold_skip elementsZ_single_succ_front !InZ_nil /=.
      split; first by tauto.
      move => []; first by tauto.
      move => [] H_fy' []. {
        move => H_x_eq; subst y'.
        contradict H_fy'.
        by rewrite H_fx.
      } {
        tauto.
      }
    }
  Qed.
        

  Lemma filterZ_single_props :
    forall f c x acc,
      interval_list_invariant (rev acc) = true ->
      (forall y' : Z, InZ y' acc -> Z.succ y' < x) ->     
      match (filterZ_single f acc x c) with
        r =>
        interval_list_invariant (List.rev r) = true /\
        (forall y', InZ y' r <-> (InZ y' acc \/
                                 (f y' = true /\ List.In y' (elementsZ_single x c))))

      end.
  Proof.
    intros f c x acc.
    move => H_inv H_acc.
    rewrite /filterZ_single.

    have H_inv' : partitionZ_aux_invariant x acc None. {
      by rewrite /partitionZ_aux_invariant /=.
    }
    move : (filterZ_single_aux_props f c x acc None H_inv').
    case_eq (filterZ_single_aux f (acc, None) x c).
    move => acc' cur' /= H_res.
    tauto.
  Qed.

  
  Lemma filterZ_aux_props :
    forall f s acc,
      interval_list_invariant s = true ->
      interval_list_invariant (rev acc) = true ->
      (forall x1 x2 : Z, InZ x1 acc -> InZ x2 s -> Z.succ x1 < x2) ->   
      match (filterZ_aux acc f s) with
        r =>
        interval_list_invariant r = true /\
        (forall y', InZ y' r <-> (InZ y' acc \/
                                 (f y' = true /\ InZ y' s)))
      end.
  Proof.
    intro f.
    induction s as [| [y c] s' IH]. {
      intros acc.
      move => _ H_inv _.
      rewrite /filterZ_aux.
      split; first assumption.
      move => y'; rewrite InZ_rev InZ_nil; tauto.
    } {
      intros acc.
      rewrite interval_list_invariant_cons.
      move => [H_gr] [H_c_neq_0] H_inv_s' H_inv H_in_acc /=.
      move : H_gr.
      rewrite interval_list_elements_greater_alt2_def => // H_gr.

      have H_pre : (forall y' : Z, InZ y' acc -> Z.succ y' < y). {
        move => x1 H_x1_in.
        apply H_in_acc => //.
        rewrite InZ_cons.
        by left; apply In_elementsZ_single_hd.
      }
      
      move : (filterZ_single_props f c y acc H_inv H_pre) => {H_pre}.
      set acc' := filterZ_single f acc y c.
      move => [H_inv'] H_in_acc'.

      have H_pre : (forall x1 x2 : Z,
                      InZ x1 acc' -> InZ x2 s' -> Z.succ x1 < x2). {
        move => x1 x2.
        rewrite H_in_acc' In_elementsZ_single.
        move => []. {
          move => H_x1_in H_x2_in.
          apply H_in_acc => //.
          rewrite InZ_cons.
          by right.
        } {
          move => [_] [_] H_x1_lt H_x2_in.
          apply Z.le_lt_trans with (m := y + Z.of_N c).
            - by apply Z.le_succ_l.
            - by apply H_gr.
        }
      }
      move : (IH acc' H_inv_s' H_inv' H_pre) => {H_pre}.

      move => [H_inv_r] H_in_r.
      split; first assumption.
      move => y'.
      rewrite H_in_r H_in_acc' InZ_cons.
      tauto.
    }
  Qed.

  Lemma filterZ_props :
    forall f s,
      interval_list_invariant s = true ->
      match (filterZ f s) with r =>
        interval_list_invariant r = true /\
        (forall y', InZ y' r <-> (f y' = true /\ InZ y' s))
      end.
  Proof.
    intros f s H_inv_s.
    rewrite /filterZ.

    have H_pre_1 : interval_list_invariant (rev nil) = true by done.
    have H_pre_2 : (forall x1 x2 : Z, InZ x1 nil -> InZ x2 s -> Z.succ x1 < x2) by done.
    
    move : (filterZ_aux_props f s nil H_inv_s H_pre_1 H_pre_2) => {H_pre_1} {H_pre_2}.
    move => [H_inv'] H_in_r.
    split; first assumption.
    move => y'.
    rewrite H_in_r InZ_nil.
    tauto.
  Qed.

  Global Instance filter_ok s f : forall `(Ok s), Ok (filter f s).
  Proof.
    move => [H_inv H_enc].
    rewrite /filter.
    set f' := (fun z : Z => f (Enc.decode z)).
    move : (filterZ_props f' s H_inv).
    move => [H_inv'] H_in_r.
    rewrite /Ok /IsOk /is_encoded_elems_list.
    split; first assumption.
    move => x /H_in_r [_] H_x_in.
    by apply H_enc.
  Qed.

  Lemma filter_spec :
   forall (s : t) (x : elt) (f : elt -> bool),
   Ok s ->      
   (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
    move => s x f H_ok.
    suff H_suff :
      (forall x, (InZ x (filter f s)) <->
                 InZ x s /\ f (Enc.decode x) = true). {
      rewrite !In_alt_def /elements !rev_map_alt_def
              -!in_rev !in_map_iff.
      setoid_rewrite H_suff.
      rewrite /InZ.
      split. {
        move => [y] [<-] [?] ?.
        split => //.
        by exists y.
      } {
        move => [] [y] [<-] ? ?.
        by exists y.
      }
    }
    rewrite /filter.
    set f' := (fun z : Z => f (Enc.decode z)).
    move : (H_ok) => [H_inv _].
    move : (filterZ_props f' s H_inv).
    move => [H_inv'] H_in_r.
    move => y; rewrite H_in_r; tauto.
  Qed.
  

  (** *** partition specification *)    

  Lemma partitionZ_single_aux_alt_def : forall f c y acc_t c_t acc_f c_f,
    partitionZ_single_aux f ((acc_t, c_t), (acc_f, c_f)) y c =
    (filterZ_single_aux f (acc_t, c_t) y c,
     filterZ_single_aux (fun x : Z => negb (f x)) (acc_f, c_f) y c).
  Proof.
    intros f.
    rewrite /partitionZ_single_aux /filterZ_single_aux.
    induction c as [| c' IH] using N.peano_ind. {
      intros y acc_t c_t acc_f c_f.
      rewrite !fold_elementsZ_single_zero //.                       } {
      intros y acc_t c_t acc_f c_f.
      rewrite !fold_elementsZ_single_succ.
      case_eq (partitionZ_fold_fun f (acc_t, c_t, (acc_f, c_f)) y) => [] [acc_t' c_t'] [acc_f' c_f'] H_fold_eq.
      rewrite IH => {IH}.
      suff : (filterZ_fold_fun f (acc_t, c_t) y = (acc_t', c_t')) /\
             (filterZ_fold_fun (fun x : Z => negb (f x)) (acc_f, c_f) y = (acc_f', c_f')). {
        move => [->] -> //.
      }
      move : H_fold_eq.
      rewrite /partitionZ_fold_fun /filterZ_fold_fun.
      case (f y); move => [<-] <- <- <- //.
    }
  Qed.
                      
  Lemma partitionZ_aux_alt_def : forall f s acc_t acc_f,
   partitionZ_aux acc_t acc_f f s =
   (filterZ_aux acc_t f s,
    filterZ_aux acc_f (fun x : Z => negb (f x)) s).
  Proof.
    intros f.
    induction s as [| [y c] s' IH]. {
      done.
    } {
      intros acc_t acc_f.
      rewrite /= /partitionZ_single /filterZ_single
              partitionZ_single_aux_alt_def.
      case (filterZ_single_aux f (acc_t, None) y c) => acc_t' c_t'.
      case (filterZ_single_aux (fun x : Z => negb (f x)) (acc_f, None) y c) => acc_f' c_f'.
      rewrite IH //.
    }
  Qed.
      
  Lemma partitionZ_alt_def : forall f s,
    partitionZ f s = (filterZ f s,
                      filterZ (fun x => negb (f x)) s).
  Proof.
    intros f s.
    rewrite /partitionZ /filterZ
            partitionZ_aux_alt_def //.    
  Qed.

  Lemma partition_alt_def : forall f s,
    partition f s = (filter f s,
                     filter (fun x => negb (f x)) s).
  Proof.
    intros f s.
    rewrite /partition /filter partitionZ_alt_def.
    done.
  Qed.


  Global Instance partition_ok1 s f : forall `(Ok s), Ok (fst (partition f s)).
  Proof.
    move => H_ok.
    rewrite partition_alt_def /fst.
    by apply filter_ok.
  Qed.  

  Global Instance partition_ok2 s f : forall `(Ok s), Ok (snd (partition f s)).
  Proof.
    move => H_ok.
    rewrite partition_alt_def /snd.
    by apply filter_ok.
  Qed.

  Lemma partition_spec1 :
   forall (s : t) (f : elt -> bool),
   Equal (fst (partition f s)) (filter f s).
  Proof.
    intros s f.
    rewrite partition_alt_def /fst /Equal //.
  Qed.

  Lemma partition_spec2 :
   forall (s : t) (f : elt -> bool),
   Ok s ->    
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
    intros s f.
    rewrite partition_alt_def /snd /Equal //.
  Qed.
  
End Raw.


(** ** Main Module 

    We can now build the invariant into the set type to obtain an instantiation
    of module type [WSetsOn]. *)

Module MSetIntervals (Enc : ElementEncode) <: SetsOn Enc.E.
  Module E := Enc.E.
  Module Raw := Raw Enc.

 (* We avoid creating induction principles for the Record *)
 Local Unset Elimination Schemes.
 Local Unset Case Analysis Schemes.

 Definition elt := Raw.elt.
 Record t_ := Mkt {this :> Raw.t; is_ok : Raw.Ok this}.
 Definition t := t_.
 Arguments Mkt this {is_ok}.
 Hint Resolve is_ok : typeclass_instances.

 Definition In (x : elt)(s : t) := Raw.In x s.(this).
 Definition Equal (s s' : t) := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s' : t) := forall a : elt, In a s -> In a s'.
 Definition Empty (s : t) := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop)(s : t) := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop)(s : t) := exists x, In x s /\ P x.

 Definition mem (x : elt)(s : t) := Raw.mem x s.(this).
 Definition add (x : elt)(s : t) : t := Mkt (Raw.add x s.(this)).
 Definition remove (x : elt)(s : t) : t := Mkt (Raw.remove x s.(this)).
 Definition singleton (x : elt) : t := Mkt (Raw.singleton x).
 Definition union (s s' : t) : t := Mkt (Raw.union s s').
 Definition inter (s s' : t) : t := Mkt (Raw.inter s s').
 Definition diff (s s' : t) : t := Mkt (Raw.diff s s').
 Definition equal (s s' : t) := Raw.equal s s'.
 Definition subset (s s' : t) := Raw.subset s s'.(this).
 Definition empty : t := Mkt Raw.empty.
 Definition is_empty (s : t) := Raw.is_empty s.
 Definition elements (s : t) : list elt := Raw.elements s.
 Definition min_elt (s : t) : option elt := Raw.min_elt s.
 Definition max_elt (s : t) : option elt := Raw.max_elt s.
 Definition choose (s : t) : option elt := Raw.choose s.
 Definition compare (s1 s2 : t) : comparison := Raw.compare s1 s2.
 Definition fold {A : Type}(f : elt -> A -> A)(s : t) : A -> A := Raw.fold f s.
 Definition cardinal (s : t) := Raw.cardinal s.
 Definition filter (f : elt -> bool)(s : t) : t := Mkt (Raw.filter f s).
 Definition for_all (f : elt -> bool)(s : t) := Raw.for_all f s.
 Definition exists_ (f : elt -> bool)(s : t) := Raw.exists_ f s.
 Definition partition (f : elt -> bool)(s : t) : t * t :=
   let p := Raw.partition f s in (Mkt (fst p), Mkt (snd p)).

 Instance In_compat : Proper (E.eq==>eq==>iff) In.
 Proof. 
   repeat red.
   move => x y H_eq_xy x' y' ->.
   rewrite /In /Raw.In.
   setoid_rewrite H_eq_xy.
   done.
 Qed.

 Definition eq : t -> t -> Prop := Equal.

 Instance eq_equiv : Equivalence eq.
 Proof. firstorder. Qed.

 Definition eq_dec : forall (s s':t), { eq s s' }+{ ~eq s s' }.
 Proof.
  intros (s,Hs) (s',Hs').
  change ({Raw.Equal s s'}+{~Raw.Equal s s'}).
  destruct (Raw.equal s s') eqn:H; [left|right];
   rewrite <- Raw.equal_spec; congruence.
 Defined.

 Definition lt : t -> t -> Prop := Raw.lt.

 Instance lt_strorder : StrictOrder lt.
 Proof.
   unfold lt.
   constructor. {
     move : Raw.lt_Irreflexive.
     rewrite /Irreflexive /complement /Reflexive.
     move => H x.
     apply H.
   } {
     move : Raw.lt_Transitive.
     rewrite /Transitive.
     move => H x y z.
     apply H.
   }
 Qed.

 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
   repeat red.
   move => [x1 H_x1_ok] [y1 H_y1_ok] H_eq.
   move => [x2 H_x2_ok] [y2 H_y2_ok].
   move : H_eq.
   rewrite /eq /lt /Equal /In /=.
   replace (forall a : elt, Raw.In a x1 <-> Raw.In a y1) with
     (Raw.Equal x1 y1) by done.
   replace (forall a : elt, Raw.In a x2 <-> Raw.In a y2) with
     (Raw.Equal x2 y2) by done.
   rewrite -!Raw.equal_spec !Raw.equal_alt_def.
   move => -> -> //.
 Qed.
 
 Section Spec.
  Variable s s' : t.
  Variable x y : elt.
  Variable f : elt -> bool.
  Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

  Lemma mem_spec : mem x s = true <-> In x s.
  Proof. exact (Raw.mem_spec _ _ _). Qed.
  Lemma equal_spec : equal s s' = true <-> Equal s s'.
  Proof. rewrite Raw.equal_spec //. Qed.
  Lemma subset_spec : subset s s' = true <-> Subset s s'.
  Proof. exact (Raw.subset_spec _ _ _ _). Qed.
  Lemma empty_spec : Empty empty.
  Proof. exact Raw.empty_spec. Qed.
  Lemma is_empty_spec : is_empty s = true <-> Empty s.
  Proof. rewrite Raw.is_empty_spec //. Qed.
  Lemma add_spec : In y (add x s) <-> E.eq y x \/ In y s.
  Proof. exact (Raw.add_spec _ _ _ _). Qed.
  Lemma remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
  Proof. exact (Raw.remove_spec _ _ _ _). Qed.
  Lemma singleton_spec : In y (singleton x) <-> E.eq y x.
  Proof. exact (Raw.singleton_spec _ _). Qed.
  Lemma union_spec : In x (union s s') <-> In x s \/ In x s'.
  Proof. exact (Raw.union_spec _ _ _ _ _). Qed.
  Lemma inter_spec : In x (inter s s') <-> In x s /\ In x s'.
  Proof. exact (Raw.inter_spec _ _ _ _ _). Qed.
  Lemma diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
  Proof. exact (Raw.diff_spec _ _ _ _ _). Qed.
  Lemma fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof. exact (@Raw.fold_spec _). Qed.
  Lemma cardinal_spec : cardinal s = length (elements s).
  Proof. exact (@Raw.cardinal_spec s). Qed.
  Lemma filter_spec : compatb f ->
    (In x (filter f s) <-> In x s /\ f x = true).
  Proof. move => _; exact (@Raw.filter_spec _ _ _ _). Qed.
  Lemma for_all_spec : compatb f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof. exact (@Raw.for_all_spec _ _ _). Qed.
  Lemma exists_spec : compatb f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof. exact (@Raw.exists_spec _ _ _). Qed.
  Lemma partition_spec1 : compatb f -> Equal (fst (partition f s)) (filter f s).
  Proof. move => _; exact (@Raw.partition_spec1 _ _). Qed.
  Lemma partition_spec2 : compatb f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof. move => _; exact (@Raw.partition_spec2 _ _ _). Qed.
  Lemma elements_spec1 : InA E.eq x (elements s) <-> In x s.
  Proof. rewrite /In /Raw.In /elements //. Qed.
  Lemma elements_spec2w : NoDupA E.eq (elements s).
  Proof. exact (Raw.elements_spec2w _ _). Qed.
  Lemma elements_spec2 : sort E.lt (elements s).  
  Proof. exact (Raw.elements_sorted _ _). Qed.
  Lemma choose_spec1 : choose s = Some x -> In x s.
  Proof. exact (Raw.choose_spec1 _ _ _). Qed.
  Lemma choose_spec2 : choose s = None -> Empty s.
  Proof. exact (Raw.choose_spec2 _). Qed.
  Lemma choose_spec3 : choose s = Some x -> choose s' = Some y ->
    Equal s s' -> E.eq x y.
  Proof.
    intros H1 H2 H3.
    suff -> : x = y. {
      apply E.eq_equiv.
    }
    move : H1 H2 H3.
    exact (Raw.choose_spec3 _ _ _ _ _ _).
  Qed.

  Lemma min_elt_spec1 : choose s = Some x -> In x s.
  Proof. exact (Raw.min_elt_spec1 _ _ _). Qed.
  Lemma min_elt_spec2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
  Proof. exact (Raw.min_elt_spec2 _ _ _ _). Qed.
  Lemma min_elt_spec3 : choose s = None -> Empty s.
  Proof. exact (Raw.min_elt_spec3 _). Qed.
  
  Lemma max_elt_spec1 : max_elt s = Some x -> In x s.
  Proof. exact (Raw.max_elt_spec1 _ _ _). Qed.
  Lemma max_elt_spec2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
  Proof. exact (Raw.max_elt_spec2 _ _ _ _). Qed.
  Lemma max_elt_spec3 : max_elt s = None -> Empty s.
  Proof. exact (Raw.max_elt_spec3 _). Qed.

  Lemma compare_spec : CompSpec eq lt s s' (compare s s').
  Proof.
    generalize s s'.
    move => [s1 H_ok_s1] [s2 H_ok_s2].
    move : (Raw.compare_spec s1 s2).
    rewrite /CompSpec /eq /Equal /In /lt /compare /=.
    replace (forall a : elt, Raw.In a s1 <-> Raw.In a s2) with
    (Raw.Equal s1 s2) by done.
    suff H_eq : (Raw.Equal s1 s2) <-> (s1 = s2). {
      move => [] H; constructor => //.
      by rewrite H_eq.
    }
    rewrite -Raw.equal_spec Raw.equal_alt_def //.
  Qed.
  
 End Spec.

End MSetIntervals.



(** ** Instantiations 

    It remains to provide instantiations for commonly used datatypes. *)

(** *** Z *)

Module ElementEncodeZ <: ElementEncode.
  Module E := Z.

  Definition encode (z : Z) := z.
  Definition decode (z : Z) := z.

  Lemma decode_encode_ok: forall (e : E.t),
    decode (encode e) = e.
  Proof. by []. Qed.

  Lemma encode_eq : forall (e1 e2 : E.t),
    (Z.eq (encode e1) (encode e2)) <-> E.eq e1 e2.
  Proof. by []. Qed.

  Lemma encode_lt : forall (e1 e2 : E.t),
    (Z.lt (encode e1) (encode e2)) <-> E.lt e1 e2.
  Proof. by []. Qed.
  
End ElementEncodeZ.


Module MSetIntervalsZ <: SetsOn Z := MSetIntervals ElementEncodeZ.

(** *** N *)

Module ElementEncodeN <: ElementEncode.
  Module E := N.

  Definition encode (n : N) := Z.of_N n.
  Definition decode (z : Z) := Z.to_N z.

  Lemma decode_encode_ok: forall (e : E.t),
    decode (encode e) = e.
  Proof. 
    intros e.
    rewrite /encode /decode N2Z.id //.
  Qed.

  Lemma encode_eq : forall (e1 e2 : E.t),
    (Z.eq (encode e1) (encode e2)) <-> E.eq e1 e2.
  Proof. 
    intros e1 e2.
    rewrite /encode /Z.eq N2Z.inj_iff /E.eq //.
  Qed.

  Lemma encode_lt : forall (e1 e2 : E.t),
    (Z.lt (encode e1) (encode e2)) <-> E.lt e1 e2.
  Proof.
    intros e1 e2.
    rewrite /encode -N2Z.inj_lt //.
  Qed.

End ElementEncodeN.

Module MSetIntervalsN <: SetsOn N := MSetIntervals ElementEncodeN.


(** *** nat *)
Module ElementEncodeNat <: ElementEncode.
  Module E := Nat.

  Definition encode (n : nat) := Z.of_nat n.
  Definition decode (z : Z) := Z.to_nat z.

  Lemma decode_encode_ok: forall (e : E.t),
    decode (encode e) = e.
  Proof. 
    intros e.
    rewrite /encode /decode Nat2Z.id //.
  Qed.

  Lemma encode_eq : forall (e1 e2 : E.t),
    (Z.eq (encode e1) (encode e2)) <-> E.eq e1 e2.
  Proof. 
    intros e1 e2.
    rewrite /encode /Z.eq Nat2Z.inj_iff /E.eq //.
  Qed.

  Lemma encode_lt : forall (e1 e2 : E.t),
    (Z.lt (encode e1) (encode e2)) <-> E.lt e1 e2.
  Proof.
    intros e1 e2.
    rewrite /encode -Nat2Z.inj_lt //.
  Qed.

End ElementEncodeNat.

Module MSetIntervalsNat <: SetsOn Nat := MSetIntervals ElementEncodeNat.



