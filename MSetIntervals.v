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

(** * Weak sets implemented by interval lists 

    This file contains an implementation of the weak set interface
    [WSetsOn] which uses internally intervals of Z. This allows some
    large sets, which naturally map to intervals of integers to be
    represented very efficiently.

    Internally intervals of Z are used. However, via an encoding
    and decoding layer, other types of elements can be handled as
    well. There are instantiations for Z, N and nat currently.
    More can be easily added.
*)

Require Import MSetInterface OrdersFacts OrdersLists.
Require Import BinNat.
Require Import ssreflect.
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
  Declare Module E : DecidableType.

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
Module Ops (Enc : ElementEncode) <: WOps Enc.E.
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

  Fixpoint elementsZ_aux'' (acc : list Z) (x : Z) (c : N) (H : Acc N.lt c) { struct H } : list Z :=
    match c as c0 return c = c0 -> list Z with
    | N0 => fun _ => acc
    | c => fun Heq => elementsZ_aux'' (x::acc) (Z.succ x) (N.pred c) (acc_pred _ _ Heq H)
    end (refl_equal _).

  Extraction Inline elementsZ_aux''.

  Definition elementsZ_aux' acc x c := elementsZ_aux'' acc x c (lt_wf_0 _).

  Fixpoint elementsZ_aux acc (s : t) : list Z := 
    match s with 
    | nil => acc
    | (x, c) :: s' => 
        elementsZ_aux (elementsZ_aux' acc x c) s'
    end.

  Definition elementsZ (s : t) : list Z := 
    elementsZ_aux nil s.

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

  (** adding an element needs to be defined carefully again in order to
      generate efficient code *)
  Fixpoint addZ_aux (acc : list (Z * N)) (x : Z) (s : t) :=
    match s with
    | nil => List.rev' ((x, (1%N))::acc)
    | (y, c) :: l =>
        match (Z.compare (Z.succ x) y) with
        | Lt => List.rev_append ((x, (1%N))::acc) s
        | Eq => List.rev_append ((x, N.succ c)::acc) l
        | Gt => match (Z.compare x (y+Z.of_N c)) with
                 | Lt => List.rev_append acc s
                 | Gt => addZ_aux ((y,c) :: acc) x l
                 | Eq => match l with
                           | nil => List.rev' ((y, N.succ c)::acc) 
                           | (z, c') :: l' => if (Z.eqb z (Z.succ x)) then
                                List.rev_append ((y,N.succ (c+c')) :: acc) l'
                             else
                                List.rev_append ((y,N.succ c) :: acc) l
                         end
                end                 
        end
    end.

  Definition addZ x s := addZ_aux nil x s.
  Definition add x s := addZ (Enc.encode x) s.

  (** [add_list] simple extension to add many elements, which then allows to
      define from_elements. *)
  Definition add_list (l : list elt) (s : t) : t :=
     List.fold_left (fun s x => add x s) l s.

  Definition from_elements (l : list elt) : t := add_list l empty.

  (** [singleton] is trivial to define *)
  Definition singleton (x : elt) : t := (Enc.encode x, 1%N) :: nil.

  Lemma singleton_alt_def : forall x, singleton x = add x empty. 
  Proof. by []. Qed.


  (** removing needs to be done with code extraction in mind again. *)
  Definition removeZ_aux_insert_guarded (x : Z) (c : N) s :=
     if (N.eqb c 0) then s else (x, c) :: s.

  Fixpoint removeZ_aux (acc : list (Z * N)) (x : Z) (s : t) : t :=
    match s with
    | nil => List.rev' acc
    | (y, c) :: l =>
        if (Z.ltb x y) then List.rev_append acc s else
        if (Z.ltb x (y+Z.of_N c)) then (
           List.rev_append (removeZ_aux_insert_guarded (Z.succ x) 
              (Z.to_N ((y+Z.of_N c)- (Z.succ x))) 
             (removeZ_aux_insert_guarded y (Z.to_N (x-y)) acc)) l
        ) else removeZ_aux ((y,c)::acc) x l
    end.

  Definition removeZ (x : Z) (s : t) : t := removeZ_aux nil x s.
  Definition remove (x : elt) (s : t) : t := removeZ (Enc.encode x) s.

  Definition remove_list (l : list elt) (s : t) : t :=
     List.fold_left (fun s x => remove x s) l s.

  (** all other operations are defined trivially (if not always efficiently)
      in terms of already defined ones. In the future it might be worth implementing
      some of them more efficiently. *)
  Definition union (s1 s2 : t) :=
    add_list (elements s1) s2.

  Definition filter (f : elt -> bool) (s : t) : t :=
    from_elements (List.filter f (elements s)).

  Definition inter (s1 s2 : t) : t :=
    filter (fun x => mem x s2) s1.

  Definition diff (s1 s2 : t) : t :=
    remove_list (elements s2) s1.

  Definition subset s s' :=
    List.forallb (fun x => mem x s') (elements s).

  Fixpoint equal (s s' : t) : bool := match s, s' with
    | nil, nil => true
    | ((x,cx)::xs), ((y,cy)::ys) => andb (Z.eqb x y) (andb (N.eqb cx cy) (equal xs ys))
    | _, _ => false
  end. 

  Definition fold {B : Type} (f : elt -> B -> B) (s : t) (i : B) : B :=
    List.fold_left (flip f) (elements s) i.

  Definition for_all (f : elt -> bool) (s : t) : bool :=
    List.forallb f (elements s).

  Definition exists_ (f : elt -> bool) (s : t) : bool :=
    List.existsb f (elements s).

  Definition partition (f : elt -> bool) (s : t) : t * t :=
    (filter f s, filter (fun x => negb (f x)) s).


  Fixpoint cardinalN c (s : t) : N := match s with
    | nil => c
    | (_,cx)::xs => cardinalN (c + cx)%N xs
  end. 

  Definition cardinal (s : t) : nat := N.to_nat (cardinalN (0%N) s).

  Definition chooseZ (s : t) : option Z :=
    match List.rev' (elementsZ s) with
    | nil => None
    | x :: _ => Some x
    end.

  Definition choose (s : t) : option elt :=
    match elements s with
      | nil => None
      | e :: _ => Some e
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

  Definition inf (x:Z) (l: t) :=
   match l with
   | nil => true
   | (y,_)::_ => Z.ltb x y
   end.

  Fixpoint isok (l : t) :=
   match l with
   | nil => true
   | (x, c) ::l => inf (x+(Z.of_N c)) l && negb (N.eqb c 0) && isok l
   end.

  Definition is_encoded_elems_list (l : list Z) : Prop :=
    (forall x, List.In x l -> exists e, Enc.encode e = x).

  Definition IsOk s := (isok s = true /\ is_encoded_elems_list (elementsZ s)).


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
      split; first done.
      move => [H_x_le H_y_lt].     
      have := Z.le_lt_trans _ _ _ H_x_le H_y_lt.
      apply Z.lt_irrefl.
    } {
      intros y x.
      rewrite elementsZ_single_succ in_app_iff IH /= N2Z.inj_succ Z.add_succ_r Z.lt_succ_r.
      split. {
        move => []. {
          move => [H_x_le H_y_le].
          split; first done.
          by apply Z.lt_le_incl.
        }
        move => [] // <-.
        split. {
          apply Z_le_add_r.
        } {
          by apply Z.le_refl.
        }
      } {
        move => [H_x_le] H_y_lt.
        apply Z.lt_eq_cases in H_y_lt as [H_y_lt | <-]. {
          by left. 
        } {
          by right; left.
        }
      }
    }
  Qed.

  Lemma In_elementsZ_single1 : forall y x,
    List.In y (elementsZ_single x (1%N)) <->
    (x = y).
  Proof.
    intros y x.
    rewrite In_elementsZ_single /= Z.add_1_r Z.lt_succ_r.
    split. {
      move => [? ?]. by apply Z.le_antisymm.
    } {
      move => ->.
      split; apply Z.le_refl.
    }
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

  Lemma elementsZ_aux''_irrel : forall c acc x H1 H2,
      elementsZ_aux'' acc x c H1 = elementsZ_aux'' acc x c H2.
  Proof.
    intro c.
    induction c using (well_founded_ind lt_wf_0).
    case_eq c. {
      intros H_c acc x; case; intro; case; intro.
      reflexivity.
    } {
      intros p H_c acc x; case; intro; case; intro.
      simpl.
      apply H.
      rewrite H_c.
      rewrite N.pos_pred_spec.
      apply N.lt_pred_l.
      discriminate.
    }
  Qed.


  Lemma elementsZ_aux'_pos : forall s x p,
      elementsZ_aux' s x (N.pos p) = elementsZ_aux' (x::s) (Z.succ x) (Pos.pred_N p).
  Proof.
    intros s x p.
    unfold elementsZ_aux'.
    unfold elementsZ_aux''.
    case: (lt_wf_0 _).
    intro.
    apply elementsZ_aux''_irrel.
  Qed.


  Lemma elementsZ_aux'_zero : forall s x,
      elementsZ_aux' s x (0%N) = s.
  Proof.
    intros s x.
    unfold elementsZ_aux'.
    by case (lt_wf_0 (0%N)); intro.
  Qed.


  Lemma elementsZ_aux'_succ : forall s x c,
      elementsZ_aux' s x (N.succ c) = elementsZ_aux' (x::s) (Z.succ x) c.
  Proof.
    intros s x c.
    case c.
    - by rewrite elementsZ_aux'_pos.
    - intro p; simpl.
      rewrite elementsZ_aux'_pos.
        by rewrite Pos.pred_N_succ.
  Qed.


  Lemma elementsZ_single_intro : forall c s x,
     elementsZ_aux' s x c =
     (List.rev (elementsZ_single x c)) ++ s.
  Proof.
    induction c as [| c' IH] using N.peano_ind. {
      intros s x.
      rewrite elementsZ_aux'_zero.
      rewrite elementsZ_single_base //.
    } {
      intros s x.
      rewrite elementsZ_aux'_succ elementsZ_single_succ_front IH.
      rewrite -app_assoc /= //.
    }
  Qed.


  Lemma elementsZ_aux_alt_def : forall s acc,
    elementsZ_aux acc s = elementsZ s ++ acc. 
  Proof.
    induction s as [| [x c] s' IH]. {
      move => acc.
      rewrite /elementsZ_aux elementsZ_nil app_nil_l //.
    } {
      move => acc.
      rewrite /elementsZ /elementsZ_aux -/elementsZ_aux !IH !elementsZ_single_intro.
      rewrite -!app_assoc app_nil_l //.
    }
  Qed.

  Lemma elementsZ_cons : forall x c s, elementsZ (((x, c) :: s) : t) = 
     ((elementsZ s) ++ (List.rev (elementsZ_single x c))). 
  Proof. 
    intros x c s.
    rewrite /elementsZ /elementsZ_aux -/elementsZ_aux.
    rewrite !elementsZ_aux_alt_def elementsZ_single_intro !app_nil_r //.
  Qed.

  Lemma elements_cons : forall x c s, elements (((x, c) :: s) : t) = 
     ((elements_single x c) ++ elements s). 
  Proof. 
    intros x c s.
    rewrite /elements /elements_single elementsZ_cons.
    rewrite !rev_map_alt_def map_app rev_app_distr map_rev rev_involutive //. 
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


  (** *** Alternative definition of addZ *)

  (** [addZ] is defined with efficient execution in mind.
      We derive first an alternative definition that demonstrates
      the intention better and is better suited for proofs. *)
  Lemma addZ_ind : 
    forall (P : Z -> list (Z * N) -> Prop),
       (* case s = nil *)
       (forall (x : Z), P x nil) ->

       (* case s = [y, c] :: l, compare (x+1) y = Eq *)
       (forall (x : Z)  (l : list (Z * N)) (c : N),
        P x ((x + 1, c) :: l)) ->

       (* case s = [y, c] :: l, compare (x+1) y = Lt *)       
       (forall (x : Z) (l : list (Z * N)) (y : Z) (c : N),
        (x + 1 ?= y) = Lt ->
        P x ((y, c) :: l)) ->

       (* case s = [y, c] :: l, compare (x+1) y = Gt, compare x (y+c) = Eq,
           l = nil *)       
       (forall (y : Z) (c : N),
        ((y + Z.of_N c) + 1 ?= y) = Gt ->
        P (y + Z.of_N c) ((y, c) :: nil)) ->

       (* case s = (y, c) :: (z, c') :: l, compare (x+1) y = Gt, compare x (y+c) = Eq,
          (z = x + 1) *)       
       (forall (l : list (Z * N)) (y : Z) (c c' : N),
        ((y + Z.of_N c) + 1 ?= y) = Gt ->
        (P (y+Z.of_N c) l) ->
        P (y+Z.of_N c) ((y, c) :: (((y+Z.of_N c) + 1, c') :: l))) ->

       (* case s = (y, c) :: (z, c') :: l, compare (x+1) y = Gt, compare x (y+c) = Eq,
          (z <> x + 1) *)       
       (forall (l : list (Z * N)) (y : Z) (c : N) (z : Z) (c' : N),
        ((y + Z.of_N c) + 1 ?= y) = Gt ->
        (z =? (y+Z.of_N c) + 1) = false ->
        (P (y+Z.of_N c) ((y, c) :: (z, c') :: l))) ->


       (* case s = (y, c) :: l, compare (x+1) y = Gt, compare x (y+c) = Lt *)   
       (forall (x : Z) (l : list (Z * N)) (y : Z) (c : N),
        (x + 1 ?= y) = Gt ->
        (x ?= y + Z.of_N c) = Lt -> 
        P x ((y, c) :: l)) ->

       (* case s = (y, c) :: l, compare (x+1) y = Gt, compare x (y+c) = Lt *)   
       (forall (x : Z)(l : list (Z * N)) (y : Z) (c : N),
        (x + 1 ?= y) = Gt ->
        (x ?= y + (Z.of_N c)) = Gt ->
        (P x l) ->
        P x ((y, c) :: l)) ->


       forall (x : Z) (s : list (Z * N)),
       P x s.
  Proof.
    intros P H1 H2 H3 H4 H5 H6 H7 H8.
    move => x s.
    remember (length s) as n.
    revert s Heqn. 
    induction n as [n IH] using Wf_nat.lt_wf_ind. 
    case. {
      move => _. apply H1.
    } {
      move => [y c] s' H_n.
      simpl in H_n.
      have IH_s': (P x s'). {
        apply (IH (length s')) => //.
        rewrite H_n //.
      }
      case_eq (x + 1 ?= y). {
        move => /Z.compare_eq_iff <-.
        apply H2.
      } {
        move => H_x1y_comp.
        by apply H3.
      } {
        move => H_x1y_comp.
        case_eq (x ?= y + Z.of_N c). {            
          move => H_x_eqb.
          move : (H_x_eqb) => /Z.compare_eq_iff H_x_eq.
          case_eq s'. {
            move => _.
            rewrite H_x_eq.
            apply H4.
            rewrite -H_x1y_comp H_x_eq //.
          } {
            move => [z c'] l H_s'.
            have IH_l: (P x l). {
              apply (IH (length l)) => //.
              rewrite H_n H_s' /=.
              apply Lt.lt_trans with (m := S (length l)) => //.
            }
            case_eq (z =? x + 1). { 
              move => /Z.eqb_eq ->.
              rewrite H_x_eq.
              apply H5. {
                rewrite -H_x1y_comp H_x_eq //.
              } {
                rewrite -H_x_eq.
                apply IH_l.
              }
            } {
              move => H_z_neq.
              rewrite H_x_eq.
              eapply H6 => //; rewrite -H_x_eq //.
            }
          }
        } {
          by apply H7.
        } {
          move => H_x_gt.
          apply H8 => //.
        }
      }
    }
  Qed.

  Lemma addZ_aux_alt_def : forall x s acc,
    addZ_aux acc x s = (List.rev acc) ++ addZ x s. 
  Proof.
    move => ? ?.
    eapply addZ_ind with (P := (fun x s => forall acc, addZ_aux acc x s = rev acc ++ addZ x s)); clear. {
      intros x acc.
      rewrite /addZ_aux /rev' -rev_alt //.
    } {
      intros x l c acc.
      rewrite /addZ /= Z.compare_refl rev_append_rev //.
    } {
      intros x l y c H_y_lt acc.
      rewrite /addZ /= H_y_lt rev_append_rev //.
    } {
      intros y c H_y_comp acc.
      rewrite /addZ /= H_y_comp Z.compare_refl /rev' -rev_alt //.
    } {
      intros l y c c' H_y_comp IH acc.
      rewrite /addZ /= H_y_comp Z.compare_refl Z.eqb_refl.
      rewrite rev_append_rev //.
    } {
      intros l y c z c' H_y_comp H_z_comp acc.
      rewrite /addZ /= H_y_comp Z.compare_refl H_z_comp.
      rewrite rev_append_rev /= //.
    } {
      intros x l y c H_y_comp H_x_comp acc.
      rewrite /addZ /= H_x_comp H_y_comp rev_append_rev //.
    } {
      intros x l y c H_y_comp H_x_comp IH acc.      
      rewrite /addZ /= H_x_comp H_y_comp.
      rewrite !IH /= -app_assoc //.
    }
  Qed.
       
  Lemma addZ_alt_def : forall x s, 
    addZ x s =
    match s with
    | nil => (x, 1%N)::nil
    | (y, c) :: l =>
        match (Z.compare (x+1) y) with
        | Lt => (x, 1%N)::s
        | Eq => (x, (c+1)%N)::l
        | Gt => match (Z.compare x (y+Z.of_N c)) with
                 | Lt => s
                 | Gt => (y,c) :: addZ x l
                 | Eq => match l with
                           | nil => (y, (c+1)%N)::nil 
                           | (z, c') :: l' => if (Z.eqb z (x + 1)) then
                                (y, (c + c' + 1)%N) :: l'
                             else
                                (y,(c+1)%N) :: (z, c') :: l'
                         end
                end                 
        end  
    end.
  Proof.
    intros x s.
    rewrite /addZ Z.add_1_r. 
    case s => //.
    move => [y c] s' /=.
    case (Z.succ x ?= y). {
      rewrite N.add_1_r //.
    } { 
      reflexivity.
    } { 
      case (x ?= y+ Z.of_N c) => //. {
        rewrite !N.add_1_r.
        case s' => //.
        move => [z c'] s'' //.
        rewrite !N.add_1_r //.
      } {
        rewrite addZ_aux_alt_def //.
      }
    }
  Qed.
   

  (** *** Alternative definition of removeZ *)

  (** [removeZ] is defined with efficient execution in mind.
      We derive first an alternative definition that demonstrates
      the intention better and is better suited for proofs. *)

  Lemma removeZ_aux_alt_def : forall s x acc,
    removeZ_aux acc x s = (List.rev acc) ++ removeZ x s. 
  Proof.
    induction s as [| [y c] s' IH]. {
      intros x acc.
      rewrite /removeZ /removeZ_aux /= app_nil_r /rev' -rev_alt //.
    } {
      intros x acc.
      rewrite /removeZ /removeZ_aux -/removeZ_aux.
      case (x <? y). {
        rewrite !rev_append_rev //=.
      } {
        case (x <? y + Z.of_N c). {
          rewrite /removeZ_aux_insert_guarded.
          case (Z.to_N (y + Z.of_N c - (Z.succ x)) =? 0)%N, (Z.to_N (x - y) =? 0)%N;
            rewrite !rev_append_rev /= // -!app_assoc /= //.
        } {
          rewrite !IH /= -app_assoc /= //.
        }
      }
    }
  Qed.

  Lemma removeZ_alt_def : forall x s,
    removeZ x s =
    match s with
    | nil => nil
    | (y, c) :: l =>
        if (Z.ltb x y) then s else
        if (Z.ltb x (y+Z.of_N c)) then (
           (removeZ_aux_insert_guarded y (Z.to_N (x-y)) 
             (removeZ_aux_insert_guarded (Z.succ x) (Z.to_N ((y+Z.of_N c)- (Z.succ x))) l))
        ) else (y, c) :: removeZ x l
    end.
  Proof.
    intros x s.
    rewrite /removeZ /=.
    case s => //.
    move => [y c] s' /=.
    case(x <? y) => //.
    case(x <? y + Z.of_N c). {
      rewrite /removeZ_aux_insert_guarded.
      case (Z.to_N (y + Z.of_N c - (Z.succ x)) =? 0)%N, (Z.to_N (x - y) =? 0)%N => //. 
    } {
      rewrite removeZ_aux_alt_def //.
    }
  Qed.
            

  (** *** Auxiliary Lemmata about Invariant *)

  Lemma inf_impl : forall x y s,
    (y <= x) -> inf x s = true -> inf y s = true.
  Proof.
    intros x y s.
    case s => //.
    move => [z c] s'.
    rewrite /inf.
    move => H_y_leq /Z.ltb_lt H_x_lt.
    apply Z.ltb_lt.
    eapply Z.le_lt_trans; eauto.
  Qed.

  Lemma Ok_nil : Ok nil <-> True. 
  Proof.
    rewrite /Ok /IsOk /isok /is_encoded_elems_list //.
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

  Lemma isok_cons : forall y c s', isok ((y, c) :: s') = true <-> 
    (inf (y+Z.of_N c) s' = true /\ ((c <> 0)%N) /\ isok s' = true). 
  Proof.
    rewrite /isok -/isok.
    intros y c s'.
    rewrite !Bool.andb_true_iff negb_true_iff.
    split. {
      move => [] [H_inf] /N.eqb_neq H_c H_s'. tauto.
    } {                           
      move => [H_inf] [/N.eqb_neq H_c] H_s'. tauto.
    }
  Qed.

  Lemma Ok_cons : forall y c s', Ok ((y, c) :: s') <-> 
    (inf (y+Z.of_N c) s' = true /\ ((c <> 0)%N) /\ 
     is_encoded_elems_list (elementsZ_single y c) /\ Ok s'). 
  Proof.
    intros y c s'.
    rewrite /Ok /IsOk isok_cons elementsZ_cons is_encoded_elems_list_app
       is_encoded_elems_list_rev.
    tauto.
  Qed.

  Lemma Nin_elements_greater : forall s y,
     inf y s = true ->
     isok s = true ->
     forall x, x <= y ->
     ~(InZ x s).
  Proof.
    induction s as [| [z c] s' IH]. {
      intros y _ _ x _.
      done.
    } {
      rewrite /inf.
      move => y /Z.ltb_lt H_y_lt /isok_cons [H_inf'] [H_c] H_s' x H_x_le.
      rewrite /InZ elementsZ_cons in_app_iff -!in_rev In_elementsZ_single. 
      move => []. {
        eapply IH; eauto.
        apply Z.le_trans with (m := z). {
          eapply Z.lt_le_incl.
          eapply Z.le_lt_trans; eauto.
        } {
          apply Z_le_add_r.
        }
      } {
        move => [H_z_leq] _; contradict H_z_leq.
        apply Z.nle_gt.
        eapply Z.le_lt_trans; eauto.
      }
    }
  Qed.

  Lemma isok_inf_nin :
     forall x s,
       isok s = true ->
       inf x s = true ->
       ~ (InZ x s). 
  Proof.
    move => x.
    induction s as [| [y c] s' IH]. {
      move => _ _.
      rewrite /InZ elementsZ_nil //.
    } {
      rewrite isok_cons.
      move => [H_inf] [_] H_ok_s' /Z.ltb_lt H_x_lt_y.
      rewrite /InZ elementsZ_cons in_app_iff -in_rev In_elementsZ_single Z.le_ngt.
      suff : inf x s' = true by tauto.
      eapply inf_impl; last apply H_inf.
      apply Z.le_trans with (m := y). {
        by apply Z.lt_le_incl.
      } {
        by apply Z_le_add_r.
      }
    } 
  Qed.

  (** *** Properties of In and InZ *)

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


  (** *** Membership specification *)
          
  Lemma memZ_spec :
   forall (s : t) (x : Z) (Hs : Ok s), memZ x s = true <-> InZ x s.
  Proof.
    induction s as [| [y c] s' IH]. {
      intros x _.
      rewrite /InZ elementsZ_nil //.
    } {    
      move => x /Ok_cons [H_inf] [H_c] [H_is_enc] H_s'.  
      rewrite /InZ /memZ elementsZ_cons -/mem.
      rewrite /isok -/isok in_app_iff -!in_rev In_elementsZ_single.

      case_eq (x <? y). {
        move => /Z.ltb_lt H_x_lt.
        split; first done.
        move => []. {
          move => H_x_in; contradict H_x_in.
          eapply Nin_elements_greater; eauto; first apply H_s'.
          apply Z.le_trans with (m := y). {
            by apply Z.lt_le_incl.
          } {
            apply Z_le_add_r.
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


  (** *** add specification *)
  Lemma addZ_spec :
   forall (s : t) (x y : Z) (Hs : Ok s),
    InZ y (addZ x s) <-> Z.eq y x \/ InZ y s.
  Proof.
    intros s x y.
    eapply addZ_ind with (P := (fun (x:Z) s => Ok s -> (InZ y (addZ x s) <-> Z.eq y x \/ InZ y s))); clear s x. {
      move => x _.
      rewrite /InZ addZ_alt_def elementsZ_cons elementsZ_nil app_nil_l -in_rev
              In_elementsZ_single1 /=.
      firstorder.
    } {
      intros x l c _.
      rewrite /InZ addZ_alt_def Z.compare_refl !elementsZ_cons !in_app_iff -!in_rev N.add_1_r
              Z.add_1_r !In_elementsZ_single N2Z.inj_succ Z.add_succ_l 
              Z.add_succ_r Z.le_succ_l Z.lt_succ_r.   
      split. {
        move => []; first by tauto.
        move => [] /Z.lt_eq_cases. 
        firstorder.
      } {
        move => [-> | ]. {
          right; split. 
            - by apply Z.le_refl.
            - by apply Z_le_add_r.
        } {
          move => []; first by tauto.
          move => [H_x_lt H_y_le].
          right; split => //.
          by apply Z.lt_le_incl.
        }
      }  
    } {
      intros x l y0 c H_y_comp _.
      rewrite /InZ addZ_alt_def H_y_comp elementsZ_cons in_app_iff
          In_elementsZ_single1.
      firstorder.
    } {
      move => y0 c H_y_comp H_ok.
      rewrite addZ_alt_def H_y_comp Z.compare_refl.   
      rewrite /InZ !elementsZ_cons elementsZ_nil !app_nil_l N.add_1_r.
      rewrite elementsZ_single_succ -!in_rev in_app_iff /=.
      firstorder.
    } {
      move => l y0 c c' H_y_comp _ _.
      rewrite addZ_alt_def H_y_comp Z.compare_refl Z.eqb_refl.
      rewrite /InZ !elementsZ_cons !in_app_iff -!in_rev.   
      have -> : (c + c' + 1 = N.succ c + c')%N. {
        rewrite -N.add_1_r. ring.
      }
      rewrite Z.add_1_r elementsZ_single_add elementsZ_single_succ !in_app_iff
              N2Z.inj_succ Z.add_succ_r.
      firstorder.
    } {
      intros l y0 c z c'.
      move => H_y_comp H_z_comp _.
      rewrite addZ_alt_def H_y_comp Z.compare_refl H_z_comp.
      rewrite /InZ !elementsZ_cons N.add_1_r !in_app_iff -!in_rev.
      rewrite elementsZ_single_succ in_app_iff /=.   
      firstorder.
    } {
      intros x l y0 c H_y_comp H_x_comp _.
      rewrite addZ_alt_def H_y_comp H_x_comp.   
      split. {
        by right.
      } {
        move => [] // ->.
        rewrite /InZ elementsZ_cons in_app_iff -in_rev In_elementsZ_single.
        right. split. {
          move : H_y_comp => /Z.compare_gt_iff.
          rewrite Z.add_1_r Z.lt_succ_r //.
        } {
          move : H_x_comp => /Z.compare_lt_iff //.
        }
      }
    } {
      intros x l y0 c H_y_comp H_x_comp IH H_ok.
      have H_ok' : Ok l. {
        move : H_ok. 
        rewrite Ok_cons.
        tauto.
      }
      rewrite addZ_alt_def H_y_comp H_x_comp.   
      unfold InZ in IH.
      rewrite /InZ !elementsZ_cons !in_app_iff -!in_rev (IH H_ok').
      firstorder.
    }
  Qed.

  Lemma addZ_isok : forall s x, isok s = true -> isok (addZ x s) = true.
  Proof. 
    intros s x.
    have H_add_1_neq : (forall x, x + 1 <> 0)%N. {
      move => x'.
      rewrite N.eq_add_0. 
      have : (1 <> 0)%N by done.
      tauto.
    }
    
    eapply addZ_ind with (P := (fun (x : Z) (s : t) => isok s = true -> 
          isok (addZ x s) = true)); clear s x. {
      move => x _ //.
    } {    
      intros x l c.
      rewrite addZ_alt_def Z.compare_refl.   
      rewrite !isok_cons.
      move => [H_inf] [H_c_neq] H_ok_l.
      split; last split => //. {
        suff -> : (x + Z.of_N (c + 1) = x + 1 + Z.of_N c) by done.
        rewrite N2Z.inj_add /=.
        ring.
      }
    } {
      intros x l y c H_y_comp.
      rewrite addZ_alt_def H_y_comp.   
      rewrite !isok_cons => [[H_inf] [H_c_neq] H_ok_l].
      split; last split; last split; last split; try done. 
      by apply Z.ltb_lt.      
    } {
      move => y c H_y_comp _.
      rewrite addZ_alt_def H_y_comp Z.compare_refl isok_cons.   
      done.      
    } {
      move => l y c c' H_y_comp IH.
      rewrite addZ_alt_def H_y_comp Z.compare_refl Z.eqb_refl.
      rewrite !isok_cons.   
      move => [H_inf1] [H_c_neq] [H_inf2] [H_c'_neq] H_ok_l.
      split; last split => //. {
        suff -> : (y + Z.of_N (c + c' + 1) =  y + Z.of_N c + 1 + Z.of_N c') by assumption.
        rewrite !N2Z.inj_add /=.
        ring.
      }
    } {
      intros l y c z c'.
      move => H_y_comp H_z_comp.
      rewrite addZ_alt_def H_y_comp Z.compare_refl H_z_comp.
      rewrite isok_cons => [] [] H_inf [] H_c_neq H_ok_l.
      rewrite isok_cons.
      split; last split; try done.
      move : H_inf.
      rewrite /inf. 
      move : H_z_comp => /Z.eqb_neq H_z_neq /Z.ltb_lt H_z_lt.
      apply Z.ltb_lt.

      have -> : Z.of_N (c + 1) = Z.of_N c + 1. {
        rewrite N2Z.inj_add //.
      }

      suff : y + (Z.of_N c + 1) <= z. {
        rewrite Z.lt_eq_cases.
        move => [] // H_z_eq.
        contradict H_z_neq.
        rewrite -H_z_eq.
        ring.
      }
      suff H_suff : (Z.pred (y + (Z.of_N c + 1)) = y + Z.of_N c). {
        apply Z.lt_pred_le.
        by rewrite H_suff.
      }
      rewrite Z.add_1_r Z.add_succ_r Z.pred_succ //.
    } {
      intros x l y c H_y_comp H_x_comp.
      rewrite addZ_alt_def H_y_comp H_x_comp //.
    } {
      intros x l y c H_y_comp H_x_comp IH.
      rewrite addZ_alt_def H_y_comp H_x_comp.   
      rewrite !isok_cons => [] [] H_inf [] H_c_neq H_ok_l.
      split; last split; try done. {
        suff : exists x0 c0 l0, addZ x l = (x0, c0)::l0 /\ (y+Z.of_N c < x0). {
           move => [x0] [c0] [l0] [->].
           rewrite /inf.
           apply Z.ltb_lt.
        }
        apply Z.compare_gt_iff in H_x_comp.
        move : H_inf.
        case l. {
          exists x, 1%N, nil.
          by rewrite addZ_alt_def.
        } {
          move =>  [z c'] l0 /Z.ltb_lt H_z_gt.
          rewrite addZ_alt_def.
          case (x + 1 ?= z); try by eauto.
          case (x ?= z + Z.of_N c'); try by eauto.
          case l0; try by eauto.
          move => [z' c''] ?.
          case (z' =? x + 1); by eauto.
        }
      } {
        apply IH => //.
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
      apply addZ_isok => //.
    } {
      intros y.
      move : (addZ_spec s (Enc.encode x) y H_ok_s).
      rewrite /InZ => ->.
      move => []. {
        move => ->.
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
    rewrite /add addZ_spec Enc.encode_eq //.
  Qed.


  (** *** remove specification *)

  Lemma isok_removeZ_aux_insert_guarded : forall x c s,
    isok s = true -> inf (x + Z.of_N c) s = true ->
    isok (removeZ_aux_insert_guarded x c s) = true.
  Proof.
    intros x c s.
    rewrite /removeZ_aux_insert_guarded.
    case_eq (c =? 0)%N => //.
    move => /N.eqb_neq.
    rewrite isok_cons.
    tauto.
  Qed.

  Lemma inf_removeZ_aux_insert_guarded : forall x c y s,
    inf y (removeZ_aux_insert_guarded x c s) = true <->
    (if (c =? 0)%N then (inf y s = true) else (y < x)).
  Proof.
    intros x c y s.
    rewrite /removeZ_aux_insert_guarded.
    case (c =? 0)%N => //.       
    rewrite /inf Z.ltb_lt //.
  Qed.


  Lemma removeZ_counter_pos_aux : forall y c x,
     x < y + Z.of_N c ->
     0 <= y + Z.of_N c - Z.succ x.
  Proof.
    intros y c x H_x_lt.
    rewrite Z.le_0_sub Z.le_succ_l.
    assumption.
  Qed.

  Lemma removeZ_isok : forall s x, isok s = true -> isok (removeZ x s) = true.
  Proof.
    intros s x.
    induction s as [| [y c] s' IH]. {
      rewrite removeZ_alt_def //.
    } {
      rewrite removeZ_alt_def.
      case_eq (x <? y) => //.
      move => /Z.ltb_ge H_y_le_x.
      case_eq (x <? y + Z.of_N c). {
        move => /Z.ltb_lt H_x_lt /isok_cons [H_inf] [H_c_neq] H_ok_s'.
        apply isok_removeZ_aux_insert_guarded; first apply isok_removeZ_aux_insert_guarded. {
          assumption.
        } {
          rewrite Z2N.id; last by apply removeZ_counter_pos_aux.
          rewrite add_add_sub_eq.
          assumption.
        } {
          rewrite /removeZ_aux_insert_guarded Z2N.id; last first. {
            by rewrite Z.le_0_sub.
          }
          rewrite add_add_sub_eq.
          case  (Z.to_N (y + Z.of_N c - Z.succ x) =? 0)%N. {
            eapply inf_impl; eauto.
            by apply Z.lt_le_incl.
          } {
            rewrite /inf.
            apply Z.ltb_lt, Z.lt_succ_diag_r.
          }
        }
      } {
        move => /Z.ltb_ge H_yc_le_x.
        rewrite !isok_cons.
        move => [H_inf] [H_c_neq] H_ok_s'.
        split; last split => //; last by apply IH. 
        move : H_inf.
        case_eq s' => //.
        move => [z c'] l' H_s'_eq.
        rewrite removeZ_alt_def.
        case (x <? z); first by eauto.
        case (x <? z + Z.of_N c'); last by eauto.
        move => /Z.ltb_lt H_lt_z.
        rewrite inf_removeZ_aux_insert_guarded.
        case (Z.to_N (x - z) =? 0)%N => //.
        rewrite inf_removeZ_aux_insert_guarded.
        case (Z.to_N (z + Z.of_N c' - Z.succ x) =? 0)%N. {
          move : H_ok_s'.
          rewrite H_s'_eq !isok_cons.
          move => [H_inf] _.
          eapply inf_impl; last apply H_inf.
          apply Z.le_trans with (m := z). {
            by apply Z.lt_le_incl.
          } {
            by apply Z_le_add_r.
          }
        } {
          rewrite Z.lt_succ_r //.
        }
      }
    }
  Qed.


  Lemma elementsZ_removeZ_aux_insert_guarded : forall x c s,
    elementsZ (removeZ_aux_insert_guarded x c s) = elementsZ ((x, c) :: s). 
  Proof.
    intros x c s.
    rewrite /removeZ_aux_insert_guarded.
    case_eq (c =? 0)%N => //.
    move => /N.eqb_eq ->.
    rewrite elementsZ_cons elementsZ_single_base /= app_nil_r //.
  Qed.
 
  Lemma removeZ_spec :
   forall (s : t) (x y : Z) (Hs : isok s = true),
    InZ y (removeZ x s) <-> InZ y s /\ ~Z.eq y x.
  Proof.
    intros s x y Hs.
    move : Hs x y.
    induction s as [| [y c] s' IH] . {
      move => _ x y.
      rewrite /=.
      firstorder.
    } {
      intros H_ok x y0.
      rewrite removeZ_alt_def.
      case_eq (x <? y). {
        move => /Z.ltb_lt H_x_lt.
        split; last tauto.
        move => H_in.
        split => // H_y0_eq.
        apply (isok_inf_nin y0 ((y, c)::s')) => //.
        rewrite /inf H_y0_eq. 
        by apply Z.ltb_lt.        
      } {
        move => /Z.ltb_ge H_y_le.
        have H_ok' : isok s' = true. {
          move : H_ok.
          rewrite isok_cons; tauto.
        } 
        move : (IH H_ok') => {IH} IH.
        case_eq (x <? y + Z.of_N c). {
          move => /Z.ltb_lt H_x_lt /=.
          rewrite /InZ elementsZ_removeZ_aux_insert_guarded !elementsZ_cons.
          rewrite elementsZ_removeZ_aux_insert_guarded elementsZ_cons !in_app_iff -!in_rev.
          rewrite !In_elementsZ_single !Z2N.id; last first. {
            by apply removeZ_counter_pos_aux.
          } {
            by rewrite Z.le_0_sub.
          }
          rewrite !add_add_sub_eq Z.le_succ_l.
          case_eq (y0 =? x). {
            move => /Z.eqb_eq ->.
            split; last first. {
              move => [_] H_neq.
              contradict H_neq => //.
            } {
              move => [[] |]. {
                move => H_in. exfalso.
                apply (isok_inf_nin x s') => //.
                move : H_ok.
                case s' => //.
                move => [z c'] s''.
                rewrite !isok_cons /inf.
                move => [] /Z.ltb_lt H_lt_x' _.
                apply Z.ltb_lt.
                eapply Z.lt_trans; eauto.
              } {
                move => [] /Z.lt_irrefl //.
              } {
                move => [_] /Z.lt_irrefl //.
              }
            } 
          }
          move => /Z.eqb_neq H_y0_neq.
          split. {
            move => H.
            split; last by apply H_y0_neq.
            move : H => [[] |]. {
              by left.
            } {
              move => [H_x_lt'] H_y0_lt.
              right; split => //.
              apply Z.le_trans with (m := x) => //.
              by apply Z.lt_le_incl.
            } {
              move => [H_y_le'] H_y0_lt.
              right; split => //.
              eapply Z.lt_trans; eauto.
            }
          } {
            move => [[]]; first by tauto.
            move => [H_y_le'] H_y0_lt _.
            case_eq (y0 <? x). {
              move => /Z.ltb_lt H_y0_lt_x.
              right. done.
            } {
              move => /Z.ltb_ge /Z.lt_eq_cases []. {
                move => H_x_lt'.
                left; right.
                done.
              } {
                move => H_x_eq.
                contradict H_y0_neq => //.
              }
            }
          } 
        } {
          move => /Z.ltb_ge H_yc_le.
          unfold InZ in IH.
          rewrite /InZ !elementsZ_cons !in_app_iff !IH.
          split; last tauto.
          move => []; first tauto.
          rewrite -!in_rev In_elementsZ_single.
          move => [H_y_le'] H_y0_lt.
          split; first by right.        
          move => H_y0_eq.
          move : H_y0_lt.
          apply Z.nlt_ge.
          by rewrite H_y0_eq.
        }
      }
    }
  Qed.


  Global Instance remove_ok s x : forall `(Ok s), Ok (remove x s).
  Proof.
    rewrite /Ok /IsOk /remove.
    move => [H_is_ok_s H_enc_s].
    split. {
      by apply removeZ_isok.
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

  (** *** union specification *)

  Global Instance union_ok s s' : forall `(Ok s, Ok s'), Ok (union s s').
  Proof.
    move => H_ok H_ok'.
    rewrite /union.
    by apply add_list_ok.
  Qed.
    
  Lemma union_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (union s s') <-> In x s \/ In x s'.
  Proof.
    intros s s' x H_ok H_ok'.
    rewrite /union add_list_spec //.
  Qed.


  (** *** filter specification *)

  Global Instance filter_ok s f : forall `(Ok s), Ok (filter f s).
  Proof.
    move => _.
    rewrite /filter /from_elements.
    apply add_list_ok, empty_ok.
  Qed.

  Lemma filter_spec :
   forall (s : t) (x : elt) (f : elt -> bool),
   Proper (Enc.E.eq==>eq) f ->
   (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
    move => s x f H_prop.
    rewrite /filter /from_elements add_list_spec  empty_spec' /In !InA_alt.
    setoid_rewrite filter_In.
    split. {
      move => [] //.
      move => [y] [H_y_eq] [H_y_in] H_fy.
      split; first by exists y.
      rewrite -H_fy.
      by f_equiv.
    } {
      move => [] [y] [H_y_eq] H_y_in H_fx.
      left. 
      exists y.
      split; last split; try assumption.
      apply Logic.eq_sym.
      rewrite -H_fx.
      by f_equiv.
    }
  Qed.


  (** *** inter specification *)

  Global Instance inter_ok s s' : forall `(Ok s, Ok s'), Ok (inter s s').
  Proof.
    intros H_ok H_ok'.
    rewrite /inter.
    by apply filter_ok.
  Qed.

  Lemma inter_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (inter s s') <-> In x s /\ In x s'.
  Proof.
    intros s s' x Hs Hs'.
    rewrite /inter.
    setoid_rewrite filter_spec. {
      by rewrite mem_spec.
    } {
      repeat red.
      intros y y' H_y_y'_eq.
      apply eq_true_iff_eq.
      rewrite !mem_spec /In.
      setoid_rewrite H_y_y'_eq.
      done.
    }
  Qed.


  (** *** diff specification *)

  Global Instance diff_ok s s' : forall `(Ok s, Ok s'), Ok (diff s s').
  Proof.
    intros ? ?.
    by apply remove_list_ok.
  Qed.

  Lemma diff_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
    intros s s' x Hs Hs'.
    rewrite /diff remove_list_spec.
    tauto.
  Qed.


  (** *** subset specification *)

  Lemma subset_spec :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s'),
   subset s s' = true <-> Subset s s'.
  Proof.
    intros s s' Hs Hs'.
    rewrite /subset forallb_forall /Subset.
    split; (
      move => H x /In_alt_def H_x_in;
      move : (H x H_x_in) => {H};
      rewrite mem_spec //
    ).
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
      move : (H_ok_s) => /Ok_cons [H_inf] [H_c] [H_enc] H_s'.
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
        eapply Nin_elements_greater; eauto; first apply H_s'.
        by apply Z.lt_le_incl.
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

  Lemma elementsZ_cons_le_start : forall x cx xs y cy ys,
     isok ((x, cx) :: xs) = true ->
     isok ((y, cy) :: ys) = true ->
     (forall z, List.In z (elementsZ ((y, cy) :: ys)) ->
                List.In z (elementsZ ((x, cx) :: xs))) ->
     (x <= y). 
  Proof.
    intros x cx xs y cy ys.
    rewrite !isok_cons.
    move => [H_inf_xs] [H_cx] H_xs [H_inf_ys] [H_cy] H_ys H.

    case_eq (x <=? y). {
      move => /Z.leb_le //.
    } {
      move => /Z.leb_gt H_y_lt.
      exfalso.
      move : (H y).
      have -> : (List.In y (elementsZ ((x, cx) :: xs)) <-> False). {
        split => //.
        rewrite elementsZ_cons in_app_iff -in_rev In_elementsZ_single.
        move => []. {
          suff : (~ InZ y xs). {
            rewrite /InZ //.
          }
          eapply Nin_elements_greater; eauto.
          eapply Z.le_trans with (m := x). {
            by apply Z.lt_le_incl.
          } {
            apply Z_le_add_r.
          }
        } {
          apply Z.lt_nge in H_y_lt.
          tauto.
        }
      } 
      have -> : (List.In y (elementsZ ((y, cy) :: ys)) <-> True). {
        split => // _.
        rewrite elementsZ_cons in_app_iff -in_rev.
        right.
        apply In_elementsZ_single_hd => //.
      } 
      tauto.
    }
  Qed.

  Lemma elementsZ_cons_le_end : forall x cx xs y cy ys,
     isok ((x, cx) :: xs) = true ->
     isok ((y, cy) :: ys) = true ->
     (x <= y + Z.of_N cy) ->
     (forall z, List.In z (elementsZ ((x, cx) :: xs)) ->
                List.In z (elementsZ ((y, cy) :: ys))) ->
     (x + Z.of_N cx <= y + Z.of_N cy). 
  Proof.
    intros x cx xs y cy ys.
    rewrite !isok_cons.
    move => [H_inf_xs] [H_cx] H_xs [H_inf_ys] [H_cy] H_ys H_x_le H.

    case_eq (x + Z.of_N cx <=? y + Z.of_N cy). {
      move => /Z.leb_le //.
    } {
      move => /Z.leb_gt H_y_lt.
      exfalso.
      move : (H (y + Z.of_N cy)).
      have -> : ((List.In (y + Z.of_N cy)) (elementsZ ((y, cy) :: ys)) <-> False). {
        split => //.
        rewrite elementsZ_cons in_app_iff -in_rev In_elementsZ_single.
        move => []. {
          suff : (~ InZ (y + Z.of_N cy) ys). {
            rewrite /InZ //.
          }
          eapply Nin_elements_greater; eauto.
          apply Z.le_refl.
        } {
          move => [_] /Z.lt_irrefl //.
        }
      } 
      have -> : (List.In (y + Z.of_N cy) (elementsZ ((x, cx) :: xs)) <-> True). {
        split => // _.
        rewrite elementsZ_cons in_app_iff -in_rev.
        right.
        rewrite In_elementsZ_single => //.
      } 
      tauto.
    }
  Qed.


  Lemma elementsZ_cons_equiv_hd : forall x cx xs y cy ys,
     isok ((x, cx) :: xs) = true ->
     isok ((y, cy) :: ys) = true ->
     (forall z, List.In z (elementsZ ((x, cx) :: xs)) <->
                List.In z (elementsZ ((y, cy) :: ys))) ->
     (x = y) /\ (cx = cy). 
  Proof.
    intros x cx xs y cy ys H_ok_xs H_ok_ys H.
    have H_xy_eq : x = y. {
      have H_x_le : (x <= y). {
        eapply (elementsZ_cons_le_start); eauto.
        intro z.
        rewrite H => //.
      } 
      have H_y_le : (y <= x). {
        eapply (elementsZ_cons_le_start); eauto.
        intro z.
        rewrite H => //.
      } 
      apply Z.le_antisymm => //.
    }
    subst.
    split => //.

    have : (y + Z.of_N cx = y + Z.of_N cy). {
      have H_cx_le : (y + Z.of_N cx <= y + Z.of_N cy). {
        eapply elementsZ_cons_le_end; eauto. {       
          apply Z_le_add_r.
        } {
          intro Z.
          rewrite H => //.
        }
      }
      have H_cy_le : (y + Z.of_N cy <= y + Z.of_N cx). {
        eapply elementsZ_cons_le_end; eauto. {       
          apply Z_le_add_r.
        } {
          intro Z.
          rewrite H => //.
        }
      }
      apply Z.le_antisymm => //.
    }
    rewrite Z.add_cancel_l.
    apply N2Z.inj.
  Qed.


  Lemma elementsZ_single_equiv : forall x cx y cy,
     (cx <> 0)%N ->
     (cy <> 0)%N ->
     (forall z, List.In z (elementsZ_single x cx) <->
                List.In z (elementsZ_single y cy)) ->
     (x = y) /\ (cx = cy). 
  Proof.
    intros x cx y cy H_cx H_cy H.
    apply elementsZ_cons_equiv_hd with (xs := nil) (ys := nil). {
      rewrite isok_cons //.
    } {
      rewrite isok_cons //.
    } {
      intro z. 
      move : (H z) => {H}.
      rewrite !elementsZ_cons !in_app_iff !elementsZ_nil -!in_rev /= => -> //.
    }
  Qed.
   

  Lemma equal_elementsZ :
    forall (s s' : t) {Hs : Ok s} {Hs' : Ok s'},
    (forall x, (InZ x s <-> InZ x s')) -> (s = s').
  Proof.
    induction s as [| [x cx] xs IH]. {
      move => [] //.
      move => [y cy ys] _ /Ok_cons [_] [H_cy] _.
      rewrite /InZ elementsZ_nil /= => H.
      exfalso.
      rewrite (H y) elementsZ_cons in_app_iff -in_rev.
      right.
      apply In_elementsZ_single_hd => //.
    } {  
      move => []. {
        move => /Ok_cons [_] [H_xc] _ _.
        rewrite /InZ elementsZ_nil /= => H.
        exfalso.
        rewrite -(H x) elementsZ_cons in_app_iff -in_rev.
        right.
        apply In_elementsZ_single_hd => //.
      } {
        move => [y cy ys] H_ok_xxs H_ok_yys. 
        rewrite /InZ.
        move => H_in.

        have [H_ok_xs H_inf_xs] : Ok xs /\ inf (x + Z.of_N cx) xs = true. {
          move : H_ok_xxs => /Ok_cons; tauto.
        }
        have [H_ok_ys H_inf_ys] : Ok ys /\ inf (y + Z.of_N cy) ys = true. {
          move : H_ok_yys => /Ok_cons. tauto.
        }
        have H_isok_xs : isok xs=true by apply H_ok_xs.
        have H_isok_ys : isok ys=true by apply H_ok_ys.

        have [H_x_eq H_cx_eq] : (x = y) /\ (cx = cy). {
          eapply elementsZ_cons_equiv_hd. 
            - by apply H_ok_xxs.
            - by apply H_ok_yys.
            - by apply H_in.
        }
        subst.

        suff -> : (xs = ys) by [].
        suff H_suff : (forall x : Z, InZ x xs <-> InZ x ys) by apply IH.

        move => z.
        move : (H_in z) => {H_in}.
        move : (Nin_elements_greater _ _ H_inf_xs H_isok_xs z).
        move : (Nin_elements_greater _ _ H_inf_ys H_isok_ys z).
        rewrite /InZ !elementsZ_cons !in_app_iff -!in_rev !In_elementsZ_single.
        move => H_nin_ys H_nin_xs H_equiv.
        split. {
          move => H_z_in.
          have : List.In z (elementsZ ys) \/ y <= z < y + Z.of_N cy. {
            rewrite -H_equiv.
            by left.
          }
          move => [] //.
          move => [_] /Z.lt_le_incl H_z_le.
          contradict H_z_in.
          by apply H_nin_xs.
        } {
          move => H_z_in.
          have : List.In z (elementsZ xs) \/ y <= z < y + Z.of_N cy. {
            rewrite H_equiv.
            by left.
          }
          move => [] //.
          move => [_] /Z.lt_le_incl H_z_le.
          contradict H_z_in.
          by apply H_nin_ys.
        }
      }
    }
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


  (** *** choose specification *)

  Lemma choose_alt_def : forall s, 
    choose s = match chooseZ s with
      | None => None
      | Some e => Some (Enc.decode e)
    end.
  Proof.
    intros s.
    rewrite /choose /chooseZ /elements /rev' rev_append_rev app_nil_r 
            rev_map_alt_def -map_rev.
    case (rev (elementsZ s)) => //.
  Qed.

  Definition choose_spec1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s. 
  Proof.   
    intros s x.
    rewrite /choose /In.
    case (elements s) => //.
    move => z l [<-].
    apply InA_cons_hd.
    apply Enc.E.eq_equiv.
  Qed.

  Definition choose_spec2 :
    forall s : t, choose s = None -> Empty s.
  Proof.   
    rewrite /choose /Empty /In.
    intro s.
    case (elements s) => //.
    move => _ a.
    rewrite InA_nil //.
  Qed.


  Lemma chooseZ_min :
    forall (s : t) (x y : Z) (Hs : Ok s),
    chooseZ s = Some x -> InZ y s -> ~ Z.lt y x.
  Proof.
    intros s x y H_ok H_min H_in H_y_lt_x.
    eapply (Nin_elements_greater s (Z.pred x)) => //; last apply H_in. {
      move : H_ok H_min.
      case s => //.
      move => [z c] s'.
      rewrite /chooseZ Ok_cons elementsZ_cons /rev' -rev_alt rev_app_distr
              rev_involutive.
      move => [_] [/N.neq_0_r] [c'] -> _.
      rewrite elementsZ_single_succ_front /=. 
      move => [->].
      apply Z.ltb_lt, Z.lt_pred_l.
    } {
      apply H_ok.
    } {
      by apply Z.lt_le_pred.
    }
  Qed.

  Lemma chooseZ_InZ :
    forall (s : t) (x : Z),
    chooseZ s = Some x -> InZ x s.
  Proof.   
    intros s x.
    rewrite /chooseZ /InZ /rev' -rev_alt in_rev.
    case (rev (elementsZ s)) => //.
    move => z l [<-] /=.
    by left.
  Qed.


  Lemma chooseZ_spec3: forall s s' x x', Ok s -> Ok s' ->
   chooseZ s = Some x -> chooseZ s' = Some x' -> Equal s s' -> x = x'.
  Proof.
    intros s s' x x' Hs Hs' Hx Hx'.
    rewrite -equal_spec equal_alt_def => H_s_eq.
    move : Hx Hx'.
    rewrite H_s_eq => -> [] //.
  Qed.

  (** *** fold specification *)

  Lemma fold_spec :
   forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (flip f) (elements s) i.
  Proof.
    intros s A i f.
    rewrite /fold //.
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
    rewrite /for_all forallb_forall /For_all //.
    split; (
      move => HH x; move : {HH} (HH x);
      rewrite In_alt_def //
    ).
  Qed.

  (** *** exists specification *)

  Lemma exists_spec :
   forall (s : t) (f : elt -> bool) (Hs : Ok s),
   Proper (Enc.E.eq==>eq) f ->
   (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof.
    intros s f Hs H.
    rewrite /exists_ /Exists existsb_exists //.
    split; (
      move => [x] [HH1 HH2]; exists x; move : HH1 HH2;
      rewrite In_alt_def //
    ).
  Qed.

  (** *** partition specification *)

  Global Instance partition_ok1 s f : forall `(Ok s), Ok (fst (partition f s)).
  Proof.
    intros H_ok.
    rewrite /partition /fst.
    by apply filter_ok.
  Qed.

  Global Instance partition_ok2 s f : forall `(Ok s), Ok (snd (partition f s)).
  Proof.
    intros H_ok.
    rewrite /partition /snd.
    by apply filter_ok.
  Qed.

  Lemma partition_spec1 :
   forall (s : t) (f : elt -> bool),
   Proper (Enc.E.eq==>eq) f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros s f H_ok.
    rewrite /partition /fst /Equal //.
  Qed.

  Lemma partition_spec2 :
   forall (s : t) (f : elt -> bool),
   Proper (Enc.E.eq==>eq) f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
    intros s f H_ok.
    rewrite /partition /snd /Equal //.
  Qed.

End Raw.


(** ** Main Module 

    We can now build the invariant into the set type to obtain an instantiation
    of module type [WSetsOn]. *)

Module MSetIntervals (Enc : ElementEncode) <: WSetsOn Enc.E.
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
 Definition choose (s : t) : option elt := Raw.choose s.
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
  Proof. exact (@Raw.filter_spec _ _ _). Qed.
  Lemma for_all_spec : compatb f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof. exact (@Raw.for_all_spec _ _ _). Qed.
  Lemma exists_spec : compatb f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof. exact (@Raw.exists_spec _ _ _). Qed.
  Lemma partition_spec1 : compatb f -> Equal (fst (partition f s)) (filter f s).
  Proof. exact (@Raw.partition_spec1 _ _). Qed.
  Lemma partition_spec2 : compatb f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof. exact (@Raw.partition_spec2 _ _). Qed.
  Lemma elements_spec1 : InA E.eq x (elements s) <-> In x s.
  Proof. rewrite /In /Raw.In /elements //. Qed.
  Lemma elements_spec2w : NoDupA E.eq (elements s).
  Proof. exact (Raw.elements_spec2w _ _). Qed.
  Lemma choose_spec1 : choose s = Some x -> In x s.
  Proof. exact (Raw.choose_spec1 _ _). Qed.
  Lemma choose_spec2 : choose s = None -> Empty s.
  Proof. exact (Raw.choose_spec2 _). Qed.

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

End ElementEncodeZ.

Module MSetIntervalsZ <: WSetsOn Z := MSetIntervals ElementEncodeZ.


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
End ElementEncodeN.

Module MSetIntervalsN <: WSetsOn N := MSetIntervals ElementEncodeN.


(** *** nat *)
Module ElementEncodeNat <: ElementEncode.
  Module E := NPeano.Nat.

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
End ElementEncodeNat.

Module MSetIntervalsNat <: WSetsOn NPeano.Nat := MSetIntervals ElementEncodeNat.

