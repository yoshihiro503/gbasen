Require Import List Program Arith Arith.Euclid Omega.
Require Import Recdef.
Require Import GBaseN.Util.

Lemma map_id_forall : forall (A: Type) (f: A -> A) (xs: list A),
  List.Forall (fun x => f x = x) xs -> map f xs = xs.
Proof.
 induction xs; [reflexivity|]. intros Hf. inversion Hf. subst x l.
 simpl. rewrite IHxs; [now rewrite H1 | now assumption].
Qed.

Fixpoint split_at {A:Type} (n: nat) (xs: list A): (list A * list A) :=
  match n, xs with
  | O, _ => ([], xs)
  | S p, [] => ([], [])
  | S p, x::xs' =>
    let '(ys1, ys2) := split_at p xs' in
    (x::ys1, ys2)
  end.

Lemma split_at_append : forall (A: Type) (n: nat) (xs left_xs right_xs: list A),
  split_at n xs = (left_xs, right_xs) -> left_xs ++ right_xs = xs.
Proof.
 induction n.
 - simpl. intros. injection H. intros. now subst.
 - simpl. intros xs left_xs right_xs. destruct xs.
   + intro H. injection H. intros. now subst.
   + case_eq (split_at n xs). intros ys1 ys2 Heq.
     intro H. injection H. intros. subst left_xs right_xs.
     now rewrite <-(IHn xs ys1 ys2 Heq).
Qed.

Lemma append_split_at_length : forall (A: Type) (n: nat) (xs ys: list A),
  length xs = n -> split_at n (xs ++ ys) = (xs, ys).
Proof.
 induction n.
 - destruct xs; [reflexivity| discriminate]. 
 - destruct xs; [discriminate|]. simpl.
   intros ys Hlen. injection Hlen. intros Hlen'. now rewrite (IHn _ _ Hlen').
Qed.

Lemma split_at_length : forall (A: Type) (n: nat) (xs left_xs right_xs: list A),
  split_at n xs = (left_xs, right_xs) -> length left_xs + length right_xs = length xs.
Proof.
 intros. now rewrite <- (split_at_append A n xs left_xs right_xs H), app_length.
Qed.

Lemma split_at_length_left : forall (A: Type) (n: nat) (xs left_xs right_xs: list A),
(*  n > 0 -> split_at n xs = (left_xs, right_xs) -> right_xs <> nil -> length left_xs = n.*)
  split_at n xs = (left_xs, right_xs) -> right_xs <> nil -> length left_xs = n.
Proof.
 induction n.
 - intros. now inversion H.
 - destruct xs.
   + simpl. intros left_xs right_xs Heq Hneq. injection Heq. intros. subst. now elim Hneq.
   + simpl. case_eq (split_at n xs). intros ys1 ys2 Hsplit xs1 xs2 Heq Hneq.
     injection Heq.  intros. subst. simpl.
     rewrite (IHn xs _ xs2); [now auto|assumption |assumption].
Qed.

Lemma split_at_length_left_le_n : forall (A: Type) (n: nat) (xs left_xs right_xs: list A),
  length xs >= n -> split_at n xs = (left_xs, right_xs) -> length left_xs = n.
Proof.
 induction n.
 - simpl. intros xs lxs rxs Hlen Heq. injection Heq. intros. now subst.
 - destruct xs; [simpl; intros; now inversion H|].
   simpl. intros lxs rxs Hlen Hsplit.
   case_eq (split_at n xs). intros ys1 ys2 Heq. rewrite Heq in Hsplit. injection Hsplit.
   intros.  subst. simpl. rewrite (IHn xs ys1 rxs); [reflexivity|omega|assumption].
Qed.

Function ntake (A:Type) (n: nat) (xs: list A) {measure List.length xs}: list (list A) :=
  match n with
  | O => [xs]
  | _ =>
    match xs with
    | [] => []
    | _ :: _ =>
      match split_at n xs with
      | (last, nil) => [last]
      | (n_xs, xs') => n_xs :: ntake A n xs'
      end
    end
  end.
 intros A n xs n0 Hn a l Hxs. rewrite <- Hxs. intros n_xs xs' a0 l0 Hxs'. rewrite <- Hxs'.
 intros Hsplit.
 subst n. rewrite <-(split_at_length _ (S n0) xs _ _ Hsplit).
 assert (length n_xs = S n0).
 - rewrite Hxs' in Hsplit.
   apply (split_at_length_left _ (S n0) xs n_xs (a0::l0)); now auto with arith.
 - rewrite H. rewrite <- (plus_O_n (length xs')) at 1.
   apply Plus.plus_lt_le_compat; now auto with arith.
Defined.

Implicit Arguments ntake.

Lemma ntake_length : forall (A:Type)(n: nat)(xs : list A),
  xs <> nil ->
  Modulo (length xs) n 0 -> List.Forall (fun ys => length ys = n) (ntake n xs).
Proof.
 intros A n xs Hneqnil Hmod. functional induction (ntake n xs).
 - destruct Hmod as [q Hq]. now inversion Hq.
 - now constructor.
 - constructor; [|now auto].
   rewrite (split_at_length_left_le_n _ n (_x0::_x1) last []); [reflexivity| | now apply e1].
   destruct Hmod as [q Hq]. inversion Hq. unfold ge. rewrite H0.
   rewrite plus_0_r.
   rewrite <- (mult_1_l n) at 1.

   apply mult_le_compat_r. destruct q.
   + rewrite mult_0_l in H0. simpl in H0. omega.
   + omega.
 - destruct xs'; [now elim y0|]. destruct n; [now elim y|]. constructor.
   + eapply split_at_length_left; [now apply e1| now auto].
   + apply IHl; [now auto |]. destruct Hmod as [q Hq]. inversion Hq as [_ Heq].
     rewrite plus_0_r in Heq.
     erewrite <- (split_at_append _ (S n) _)in Heq; [|now apply e1].
     rewrite app_length in Heq. exists (pred q). constructor; [now apply lt_0_Sn|].
     rewrite plus_0_r.
     cut (length n_xs + length (a::xs') = length n_xs + pred q * S n).
     * omega.
     * rewrite Heq.
       erewrite (split_at_length_left _ (S n)); [|now apply e1|now auto].
       destruct q; [simpl in Heq; omega |]. rewrite <- pred_Sn. ring.
Qed.

Fixpoint concat {A: Type} (xss: list (list A)) :=
  match xss with
  | nil => nil
  | xs :: xss' => xs ++ concat xss'
  end.

Definition concat_map {A B:Type} (f: A -> list B) (xs: list A) :=
  concat (List.map f xs).

Lemma concat_ntake: forall (A: Type) (n: nat) (xs: list A),
  concat (ntake n xs) = xs.
Proof.
 intros. functional induction (ntake n xs).
 - simpl. now apply app_nil_r.
 - now simpl.
 - now rewrite <- (split_at_append _ n _ last [] e1).
 - simpl. rewrite IHl. now rewrite (split_at_append _ n _ _ _ e1).
Qed.

Lemma ntake_concat_rectangle: forall (A: Type) (n: nat) (xss: list (list A)),
  n > 0 -> Forall (fun xs => length xs = n) xss -> ntake n (concat xss) = xss.
Proof.
 induction xss.
 - intros Hn _. simpl. rewrite ntake_equation. now destruct n; [inversion Hn|].
 - intros Hn Hall. simpl. rewrite ntake_equation. destruct n; [inversion Hn |].
   inversion Hall as [|x l Hhd Htl]. subst x l.
   destruct a as [|x xs]; [discriminate Hhd|].
   rewrite append_split_at_length; [|assumption]. simpl.
   rewrite IHxss; [|assumption|assumption]. destruct xss; [reflexivity|].
   inversion Htl as [|xs' xss' Htlhd _]. subst l xss.
   destruct xs'; [discriminate Htlhd|]. reflexivity.
Qed.

Lemma append_ntake: forall (A: Type) (n: nat) (xs ys: list A),
  n > 0 ->
  length xs = n -> ntake n (xs ++ ys) = xs :: ntake n ys.
Proof.
 intros. rewrite ntake_equation. destruct n; [now auto with arith|].
 destruct xs; [discriminate H0|]. simpl. injection H0. intros Hlen.
 rewrite append_split_at_length; [|assumption].
 destruct ys.
 - now rewrite ntake_equation.
 - reflexivity.
Qed.

Lemma ntake_1: forall (A: Type) (n: nat) (xs: list A),
  n > 0 -> length xs = n -> ntake n xs = [xs].
Proof.
 intros A n xs Hn Hlen. rewrite <-(app_nil_r xs) at 1. rewrite (append_ntake _ _ _ _ Hn Hlen).
 rewrite ntake_equation. now destruct Hn.
Qed.

Lemma concat_length_rectangle: forall (A: Type) (n: nat) (xss: list (list A)),
  Forall (fun xs => length xs = n) xss -> length (concat xss) = n * length xss.
Proof.
 induction xss.
 - intros _. now auto with arith.
 - intros Hall. inversion Hall. subst x l.
   simpl. rewrite app_length. rewrite IHxss; [|assumption]. rewrite H1. ring.
Qed.

Fixpoint repeat {A: Type} (x: A) (n: nat) : list A :=
  match n with
  | O => nil
  | S p => x :: repeat x p
  end.

Lemma repeat_length : forall (A: Type) (x: A) (n: nat),
  length (repeat x n) = n.
Proof.
 induction n; [reflexivity|]. simpl. now rewrite IHn.
Qed.

Definition take {A : Type} (n: nat) (xs: list A) :=
  let '(xs1, _) := split_at n xs in
  xs1.

Definition drop_right {A: Type} (n: nat) (xs: list A) := take (length xs - n) xs.

Lemma drop_right_append: forall (A: Type) (n: nat) (xs ys: list A),
  length ys = n -> drop_right n (xs ++ ys) = xs.
Proof.
 intros A n xs ys Hlen. unfold drop_right, take.
 rewrite app_length, Hlen.
 cutrewrite (length xs + n - n = length xs); [| omega].
 rewrite append_split_at_length; reflexivity.
Qed.

Fixpoint split_last {A: Type} (dummy: A) (xs: list A) :=
  match xs with
  | nil => (nil, dummy)
  | x :: nil => (nil, x)
  | x :: xs' =>
    let '(lefts, last) := split_last dummy xs' in
    (x::lefts, last)
  end.
               
Lemma split_last_append: forall (A:Type) (dummy x: A) xs,
  split_last dummy (xs ++ [x]) = (xs, x).
Proof.
 induction xs; [reflexivity|].
 simpl. rewrite IHxs. now destruct xs.
Qed.

Lemma Forall_map: forall (A B: Type) (f: A -> B)(p: B -> Prop) xs,
  Forall (fun x => p (f x)) xs -> Forall p (map f xs).
Proof.
 intros. apply Forall_forall. intros y Hin. rewrite Forall_forall in H.
 rewrite (in_map_iff f xs y) in Hin. destruct Hin as [x Hx]. destruct Hx as [Hx1 Hx2].
 rewrite <- Hx1. apply H. assumption.
Qed.