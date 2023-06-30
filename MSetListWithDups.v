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

(** * Weak sets implemented as lists with duplicates 

    This file contains an implementation of the weak set interface
    [WSetsOnWithDupsExtra]. As a datatype unsorted lists are used
    that might contain duplicates. 

    This implementation is useful, if one needs very efficient
    insert and union operation, and can guarantee that one does not
    add too many duplicates. The operation [elements_dist] is implemented
    by sorting the list first. Therefore this instantiation can only
    be used if the element type is ordered. 
*)


Require Export MSetInterface.
Require Import mathcomp.ssreflect.ssreflect.
Require Import List OrdersFacts OrdersLists.
Require Import Sorting Permutation.
Require Import MSetWithDups.




(** ** Removing duplicates from sorted lists

    The following module [RemoveDupsFromSorted] defines an operation
    [remove_dups_from_sortedA] that removes duplicates from a sorted
    list. In order to talk about sorted lists, the element type needs
    to be ordered.

    This function is combined with a sort function to get a function
    [remove_dups_by_sortingA] to sort unsorted lists and then remove
    duplicates.  *)
Module RemoveDupsFromSorted (Import X:OrderedType).


  (** First, we need some infrastructure for our ordered type *)
  Module Import MX := OrderedTypeFacts X.

  Module Import XTotalLeBool <: TotalLeBool.
    Definition t := X.t.
    Definition leb x y := 
      match X.compare x y with
        | Lt => true
        | Eq => true
        | Gt => false
      end.

    Infix "<=?" := leb (at level 35).

    Theorem leb_total : forall (a1 a2 : t), (a1 <=? a2 = true) \/ (a2 <=? a1 = true).
    Proof.
      intros a1 a2.
      unfold leb.
      rewrite (compare_antisym a1 a2).
      case (X.compare a1 a2); rewrite /=; tauto. 
    Qed.

    Definition le x y := (leb x y = true).
  End XTotalLeBool.
   
  Lemma eqb_eq_alt : forall x y, eqb x y = true <-> eq x y. 
  Proof.
    intros x y.
    rewrite eqb_alt -compare_eq_iff.
    case (compare x y) => //.
  Qed.



  (** Now we can define our main function *)
  Fixpoint remove_dups_from_sortedA_aux (acc : list t) (l : list t) : list t :=
    match l with
    | nil => List.rev' acc
    | x :: xs => 
       match xs with 
       | nil => List.rev' (x :: acc)
       | y :: ys => 
           if eqb x y then
             remove_dups_from_sortedA_aux acc xs
           else 
             remove_dups_from_sortedA_aux (x::acc) xs
       end
    end.

  Definition remove_dups_from_sortedA := remove_dups_from_sortedA_aux (nil : list t).

  (** We can prove some technical lemmata *)
  Lemma remove_dups_from_sortedA_aux_alt : forall (l : list X.t) acc,
    remove_dups_from_sortedA_aux acc l =
    List.rev acc ++ (remove_dups_from_sortedA l).
  Proof.
    unfold remove_dups_from_sortedA.
    induction l as [| x xs IH] => acc. {
      rewrite /remove_dups_from_sortedA_aux /rev' -!rev_alt /= app_nil_r //.
    } {
      rewrite /=.
      case_eq xs. {
        rewrite /rev' -!rev_alt //.
      } {
        move => y ys H_xs_eq.
        rewrite -!H_xs_eq !(IH acc) !(IH (x :: acc)) (IH (x::nil)).
        case (eqb x y) => //.
        rewrite /= -app_assoc //.
      }
    }
  Qed.

  Lemma remove_dups_from_sortedA_alt :
    forall (l : list t),
    remove_dups_from_sortedA l =
    match l with
    | nil => nil
    | x :: xs => 
       match xs with 
       | nil => l
       | y :: ys => 
           if eqb x y then
             remove_dups_from_sortedA xs
           else 
             x :: remove_dups_from_sortedA xs
       end
    end.
  Proof.
    case. {
      done.
    } {
      intros x xs.
      rewrite /remove_dups_from_sortedA /= /rev' /=.
      case xs => //.
      move => y ys.
      rewrite !remove_dups_from_sortedA_aux_alt /= //.
    }
  Qed.

  Lemma remove_dups_from_sortedA_hd : 
      forall x xs,
      exists (x':t) xs',
        remove_dups_from_sortedA (x :: xs) =
        (x' :: xs') /\ (eqb x x' = true).
  Proof.
    intros x xs.
    move : x;
    induction xs as [| y ys IH] => x. {
      rewrite remove_dups_from_sortedA_alt.
      exists x, nil.
      split; first reflexivity.
      rewrite eqb_alt compare_refl //.
    } {
      rewrite remove_dups_from_sortedA_alt.
      case_eq (eqb x y); last first. {
        move => _.
        exists x, (remove_dups_from_sortedA (y :: ys)).
        split; first reflexivity.
        rewrite eqb_alt compare_refl //.
      } {
        move => H_eqb_xy.
        move : (IH y) => {IH} [x'] [xs'] [->] H_eqb_yx'.
        exists x', xs'.
        split; first done.
        move : H_eqb_xy H_eqb_yx'.
        rewrite !eqb_eq_alt.
        apply MX.eq_trans.
      }
    }
  Qed.


  (** Finally we get our main result for removing duplicates from sorted lists *)
  Lemma remove_dups_from_sortedA_spec : 
    forall (l : list t),
      Sorted le l ->
      let l' := remove_dups_from_sortedA l in (
    
      Sorted lt l' /\
      NoDupA eq l' /\
      (forall x, InA eq x l <-> InA eq x l')).
  Proof.
    simpl.
    induction l as [| x xs IH]. { 
      rewrite remove_dups_from_sortedA_alt.
      done.
    } {
      rewrite remove_dups_from_sortedA_alt.
      move : IH.
      case xs => {xs}. {
        move => _.
        split; last split. {
          apply Sorted_cons => //.   
        } {
          apply NoDupA_singleton.
        } {
          done.
        }
      } {
        move => y ys IH H_sorted_x_y_ys.
        apply Sorted_inv in H_sorted_x_y_ys as [H_sorted_y_ys H_hd_rel].
        apply HdRel_inv in H_hd_rel.

        have :  exists y' ys',
          remove_dups_from_sortedA (y :: ys) = y' :: ys' /\
          eqb y y' = true. {
          apply remove_dups_from_sortedA_hd => //.
        }
        move => [y'] [ys'] [H_yys'_intro] /eqb_eq_alt H_eq_y_y'.

        move : (IH H_sorted_y_ys). 
        rewrite !H_yys'_intro. 
        move => {IH} [IH1] [IH2] IH3.

        case_eq (eqb x y). {
          rewrite eqb_eq_alt => H_eq_x_y.
          split => //.
          split => //.
          move => x'.
          rewrite InA_cons IH3.
          split; last tauto.
          move => [] //.
          move => H_eq_x'_x.
          apply InA_cons_hd.
          apply eq_trans with (y := x) => //.
          apply eq_trans with (y := y) => //.
        }
        move => H_neqb_x_y.

        have H_sorted : Sorted lt (x :: y' :: ys'). {
          apply Sorted_cons => //.
          apply HdRel_cons.
          rewrite -compare_lt_iff.
          suff : (compare x y = Lt). {
            setoid_rewrite compare_compat; eauto;
              apply eq_refl.
          }
          move : H_hd_rel H_neqb_x_y.
          rewrite eqb_alt /le /leb.
          case (compare x y) => //.
        }
        split; last split. {
          assumption.
        } {
          apply NoDupA_cons => //.

          move => /InA_alt [x'] [H_eq_xx'] H_in_x'.
          have : Forall (lt x) (y' :: ys'). {
            apply Sorted_extends => //.      
            rewrite /Relations_1.Transitive.
            by apply lt_trans.
          }
          rewrite Forall_forall => H_forall.       
          move : (H_forall _ H_in_x') => {H_forall}.
          move : H_eq_xx'.
          rewrite -compare_lt_iff -compare_eq_iff.
          move => -> //.
        } {
          move => x0.
          rewrite !(InA_cons eq x0 x) IH3 //.
        }
      }
    }
  Qed.



  (** Next, we combine it with sorting *)
  Module Import XSort := Sort XTotalLeBool.

  Definition remove_dups_by_sortingA (l : list t) : list t :=
    remove_dups_from_sortedA (XSort.sort l).

  Lemma remove_dups_by_sortingA_spec : 
    forall (l : list t),
      let l' := remove_dups_by_sortingA l in (
    
      Sorted lt l' /\
      NoDupA eq l' /\
      (forall x, InA eq x l <-> InA eq x l')).
  Proof.
    intro l.

    suff : (forall x : X.t, InA eq x (sort l) <-> InA eq x l) /\
           Sorted le (sort l). {
      
      unfold remove_dups_by_sortingA.
      move : (remove_dups_from_sortedA_spec (sort l)).
      simpl.
      move => H_spec [H_in_sort H_sorted_sort].
      move : (H_spec H_sorted_sort).
      move => [H1] [H2] H3.
      split => //.
      split => //.
      move => x.
      rewrite -H_in_sort H3 //.
    }

    split. {
      have H_in_sort : forall x, List.In x (XSort.sort l) <-> List.In x l. {
        intros x.
        have H_perm := (XSort.Permuted_sort l).
        split; apply Permutation_in => //.
        by apply Permutation_sym.
      }

      intros x.
      rewrite !InA_alt.
      setoid_rewrite H_in_sort => //.
    } {
      move : (Sorted_sort l).
      rewrite /is_true /le /leb //.
    }
  Qed.

End RemoveDupsFromSorted.


(** ** Operations Module

With removing duplicates defined, we can implement
the operations for our set implementation easily. 
*)

Module Ops (X:OrderedType) <: WOps X.

  Module RDFS := RemoveDupsFromSorted X.
  Module Import MX := OrderedTypeFacts X.

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := nil.

  Definition is_empty (l : t) := match l with nil => true | _ => false end. 
  Fixpoint mem (x : elt) (s : t) : bool :=
    match s with
    | nil => false
    | y :: l =>
           match X.compare x y with
               Eq => true 
             | _ => mem x l
           end
    end.

  Definition add x (s : t) := x :: s.
  Definition singleton (x : elt) := x :: nil.

  Fixpoint rev_filter_aux acc (f : elt -> bool) s :=
    match s with
       nil => acc
     | (x :: xs) => rev_filter_aux (if (f x) then (x :: acc) else acc) f xs
    end.
  Definition rev_filter := rev_filter_aux nil.

  Definition filter (f : elt -> bool) (s : t) : t := rev_filter f s.

  Definition remove x s :=
    rev_filter (fun y => match X.compare x y with Eq => false | _ => true end) s.

  Definition union (s1 s2 : t) : t :=
    List.rev_append s2 s1.

  Definition inter (s1 s2 : t) : t :=
    rev_filter (fun y => mem y s2) s1.

  Definition elements (x : t) : list elt := x.

  Definition elements_dist (x : t) : list elt := 
    RDFS.remove_dups_by_sortingA x.

  Definition fold {B : Type} (f : elt -> B -> B) (s : t) (i : B) : B :=
    fold_left (flip f) (elements s) i.

  Definition diff (s s' : t) : t := fold remove s' s.

  Definition subset (s s' : t) : bool := 
    List.forallb (fun x => mem x s') s.

  Definition equal (s s' : t) : bool := andb (subset s s') (subset s' s).

  Fixpoint for_all (f : elt -> bool) (s : t) : bool :=
    match s with
    | nil => true
    | x :: l => if f x then for_all f l else false
    end.

  Fixpoint exists_ (f : elt -> bool) (s : t) : bool :=
    match s with
    | nil => false
    | x :: l => if f x then true else exists_ f l
    end.

  Fixpoint partition_aux (a1 a2 : t) (f : elt -> bool) (s : t) : t * t :=
    match s with
    | nil => (a1, a2)
    | x :: l =>
        if f x then partition_aux (x :: a1) a2 f l else 
                    partition_aux a1 (x :: a2) f l
    end.

  Definition partition := partition_aux nil nil.
 
  Definition cardinal (s : t) : nat := length (elements_dist s).

  Definition choose (s : t) : option elt :=
     match s with
      | nil => None
      | x::_ => Some x
     end.

End Ops.


(** ** Main Module

    Using these operations, we can define the main functor. For this,
    we need to prove that the provided operations do indeed satisfy
    the weak set interface. This is mostly straightforward and
    unsurprising. The only interesting part is that removing
    duplicates from a sorted list behaves as expected. This has
    however already been proved in module [RemoveDupsFromSorted].
  *)
Module Make (E:OrderedType) <: WSetsOnWithDupsExtra E.
  Include Ops E.
  Import MX.

  (** ** Proofs of set operation specifications. *)
  (** Logical predicates *)
  Definition In x (s : t) := SetoidList.InA E.eq x s.

  #[local] Instance In_compat : Proper (E.eq==>eq==>iff) In.
  Proof. repeat red. intros. rewrite H H0. auto. Qed.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
  Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

  Definition eq : t -> t -> Prop := Equal.
  Lemma eq_equiv : Equivalence eq. 
  Proof. 
    constructor. {
      done.
    } {
      by constructor; rewrite H.
    } {
      by constructor; rewrite H H0.
    }
  Qed.

 
  (** Specifications of set operators *)

  Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

  Lemma mem_spec : forall s x, mem x s = true <-> In x s. 
  Proof. 
    induction s as [| y s' IH]. {
      move => x.
      rewrite /= /In InA_nil.
      split => //.
    } {
      move => x.
      rewrite /= /In InA_cons. 
      move : (MX.compare_eq_iff x y).  
      case (E.compare x y). {
        tauto.
      } {
        rewrite IH; intuition; inversion H1.
      } {
        rewrite IH; intuition; inversion H1.
      } 
    }
 Qed.
 
  Lemma subset_spec : forall s s', subset s s' = true <-> s[<=]s'.
  Proof.
    intros s s'.
    rewrite /subset forallb_forall /Subset /In.
    split. {
      move => H z /InA_alt [] x [H_z_eq] H_in.
      move : (H _ H_in).
      rewrite mem_spec.
      setoid_replace z with x => //. 
    } {
      move => H z H_in.
      rewrite mem_spec.
      apply H, In_InA => //.
      apply E.eq_equiv.
    }
  Qed.

  Lemma equal_spec : forall s s', equal s s' = true <-> s[=]s'.
  Proof. 
    intros s s'.
    rewrite /Equal /equal Bool.andb_true_iff !subset_spec /Subset.
    split. {
      move => [H1 H2] a.
      split. 
        - by apply H1.
        - by apply H2.
    } {
      move => H.
      split; move => a; rewrite H //.
    }
  Qed.


  Lemma eq_dec :  forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y.
    change ({Equal x y}+{~Equal x y}).
    destruct (equal x y) eqn:H; [left|right];
     rewrite <- equal_spec; congruence.
  Qed.

  Lemma empty_spec : Empty empty.
  Proof. rewrite /Empty /empty /In. move => a /InA_nil //. Qed.
  
  Lemma is_empty_spec : forall s, is_empty s = true <-> Empty s. 
  Proof.
    rewrite /is_empty /Empty /In.
    case; split => //. {
      move => _ a.
      rewrite InA_nil //.
    } {
      move => H; contradiction (H a).
      apply InA_cons_hd.
      apply Equivalence_Reflexive.
    }
  Qed.

  Lemma add_spec : forall s x y, In y (add x s) <-> E.eq y x \/ In y s.
  Proof. 
    intros s x y.
    rewrite /add /In InA_cons //.
  Qed.

  Lemma singleton_spec : forall x y, In y (singleton x) <-> E.eq y x.
  Proof. 
    intros x y.
    rewrite /singleton /In InA_cons.
    split. {
      move => [] // /InA_nil //.
    } {
      by left.
    }
  Qed.       

  Lemma rev_filter_aux_spec : forall s acc x f, compatb f ->
    (In x (rev_filter_aux acc f s) <-> (In x s /\ f x = true) \/ (In x acc)).
  Proof. 
    intros s acc x f H_compat.
    move : x acc.
    induction s as [| y s' IH]. {
      intros x acc.
      rewrite /rev_filter_aux /In InA_nil.
      tauto.
    } {
      intros x acc.      
      rewrite /= IH /In.
      case_eq (f y) => H_fy; rewrite !InA_cons; intuition. {
        left.
        split; first by left.
        setoid_replace x with y => //. 
      } {
        contradict H1.
        setoid_replace x with y => //. 
        by rewrite H_fy.
      }
    }
  Qed.

  Lemma filter_spec : forall s x f, compatb f ->
    (In x (filter f s) <-> In x s /\ f x = true).
  Proof. 
    intros s x f H_compat.
    rewrite /filter /rev_filter rev_filter_aux_spec /In InA_nil.
    tauto.
  Qed.

  Lemma remove_spec : forall s x y, In y (remove x s) <-> In y s /\ ~E.eq y x.
  Proof.
    intros s x y.
    rewrite /remove /rev_filter. 
    have H_compat : compatb ((fun y0 : elt =>
         match E.compare x y0 with
         | Eq => false
         | _ => true
         end)). {
      repeat red; intros.
      setoid_replace x0 with y0 => //.
    }
    rewrite rev_filter_aux_spec /In InA_nil.
    have -> : (E.eq y x <-> E.eq x y). {
      split; move => ?; by apply Equivalence_Symmetric.
    }
    rewrite -compare_eq_iff.
    case (E.compare x y). {
      intuition.
    } {
      intuition.
      inversion H0.
    } {
      intuition.
      inversion H0.
    }
  Qed.


  Lemma union_spec : forall s s' x, In x (union s s') <-> In x s \/ In x s'.
  Proof.
    intros s s' x.
    rewrite /union /In rev_append_rev InA_app_iff InA_rev; tauto.
  Qed.
   
  Lemma inter_spec : forall s s' x, In x (inter s s') <-> In x s /\ In x s'.
  Proof.
    intros s s' x.
    have H_compat : compatb (fun y : elt => mem y s'). {
      repeat red; intros.
      suff : ( mem x0 s' = true <-> mem y s' = true). {
        case (mem y s'), (mem x0 s'); intuition.
      }
      rewrite !mem_spec /In.
      setoid_replace x0 with y => //.
    }
    rewrite /inter rev_filter_aux_spec mem_spec /In InA_nil.
    tauto.
  Qed.



  Lemma fold_spec : forall s (A : Type) (i : A) (f : elt -> A -> A),
    fold f s i = fold_left (flip f) (elements s) i.
  Proof. done. Qed.

  Lemma elements_spec1 : forall s x, InA E.eq x (elements s) <-> In x s.
  Proof.
    intros s x.
    rewrite /elements /In //.
  Qed.

  Lemma diff_spec : forall s s' x, In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
    intros s s' x.
    rewrite /diff fold_spec -(elements_spec1 s').
    move : s.
    induction (elements s') as [| y ys IH] => s. {
      rewrite InA_nil /=; tauto.
    } {
      rewrite /= IH InA_cons /flip remove_spec.    
      tauto.
    }
  Qed.

  Lemma cardinal_spec : forall s, cardinal s = length (elements_dist s).
  Proof. rewrite /cardinal //. Qed.

  Lemma for_all_spec : forall s f, compatb f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof.
    intros s f H_compat.
    rewrite /For_all.
    induction s as [| x xs IH]. {
      rewrite /= /In.
      split => //.
      move => _ x /InA_nil //.
    } {
      rewrite /=.
      case_eq (f x) => H_fx. {
        rewrite IH.
        split. {
          move => H x' /InA_cons []. {
            move => -> //.
          } {
            apply H.
          }
        } {
          move => H x' H_in.
          apply H.
          apply InA_cons.
          by right.
        } 
      } {
        split => //.
        move => H. 
        suff : f x = true. {
          rewrite H_fx //.
        }
        apply H.
        apply InA_cons_hd.
        apply (@Equivalence_Reflexive _ _ E.eq_equiv).
      }
    }
  Qed.
   
  Lemma exists_spec : forall s f, compatb f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof.
    intros s f H_compat.
    rewrite /Exists.
    induction s as [| x xs IH]. {
      rewrite /= /In.
      split => //.
      move => [x] [] /InA_nil //.
    } {
      rewrite /=.
      case_eq (f x) => H_fx. {
        split => // _.
        exists x.
        split => //.
        apply InA_cons_hd.
        apply (@Equivalence_Reflexive _ _ E.eq_equiv).
      } {
        rewrite IH.
        split. {
          move => [x'] [H_in] H_fx'.
          exists x'.
          split => //.
          apply InA_cons.
          by right.
        } {
          move => [x'] [] /InA_cons []. {
            move => ->.
            rewrite H_fx //.
          } {
            by exists x'.
          }
        }
      } 
    }
  Qed.

  Lemma partition_aux_spec : forall a1 a2 s f,
    (partition_aux a1 a2 f s = (rev_filter_aux a1 f s, rev_filter_aux a2 (fun x => negb (f x)) s)).
  Proof. 
    move => a1 a2 s f.
    move : a1 a2.
    induction s as [| x xs IH]. {
      rewrite /partition_aux /rev_filter_aux //.
    } {
      intros a1 a2.
      rewrite /= IH.
      case (f x) => //.

    }
  Qed.

  Lemma partition_spec1 : forall s f, compatb f ->
    fst (partition f s) [=] filter f s.
  Proof. 
    move => s f _.
    rewrite /partition partition_aux_spec /fst /filter /rev_filter //.
  Qed.

  Lemma partition_spec2 : forall s f, compatb f ->
    snd (partition f s) [=] filter (fun x => negb (f x)) s.
  Proof. 
    move => s f _.
    rewrite /partition partition_aux_spec /snd /filter /rev_filter //.
  Qed.

  Lemma choose_spec1 : forall s x, choose s = Some x -> In x s.
  Proof. 
   move => [] // y s' x [->]. 
   rewrite /In.
   apply InA_cons_hd.
   apply Equivalence_Reflexive.
  Qed.

  Lemma choose_spec2 : forall s, choose s = None -> Empty s.
  Proof. move => [] // _ a. rewrite /In InA_nil //. Qed.

  Lemma elements_dist_spec_full :
    forall s,
      Sorted E.lt (elements_dist s) /\
      NoDupA E.eq (elements_dist s) /\
      (forall x, InA E.eq x (elements_dist s) <-> InA E.eq x (elements s)).
  Proof.
    move => s.
    rewrite /elements_dist /elements.
    move : (RDFS.remove_dups_by_sortingA_spec s).
    simpl.
    firstorder.
  Qed.

  Lemma elements_dist_spec1 : forall x s, InA E.eq x (elements_dist s) <->
                                          InA E.eq x (elements s).
  Proof. intros; apply elements_dist_spec_full. Qed.

  Lemma elements_dist_spec2w : forall s, NoDupA E.eq (elements_dist s).
  Proof. intros; apply elements_dist_spec_full. Qed.

End Make.
