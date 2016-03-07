Require Import Arith List Program Ascii.

Definition revapply {A B: Type} (x: A) (f: A -> B) : B := f x.

Infix "|>" := revapply (left associativity, at level 40). (*level???*)

Definition compose {A B C: Type} (g: B -> C) (f: A -> B) (x: A) :=
  g (f x).

Inductive EucDiv a b q r : Prop :=
  CEucDiv : r < b -> a = q * b + r -> EucDiv a b q r.
Definition Modulo a b r : Prop := exists q, EucDiv a b q r.
Definition Quotient a b q: Prop := exists r, EucDiv a b q r.

Lemma Modulo_n_n : forall n, n > 0 -> Modulo n n 0.
Proof.
 intros n. exists 1. constructor; [auto with arith|ring].
Qed.

Lemma Modulo_0 : forall b r, Modulo 0 b r -> r = 0.
Proof.
 intros b r Hmod. destruct Hmod as [q Hq]. inversion Hq.
 destruct r; [reflexivity| now rewrite plus_comm in H0].
Qed.

Definition byte_size := 8.
Definition bits_of_byte byte :=
  let '(Ascii a b c d  e f g h) := byte in
  [h; g; f; e;  d; c; b; a].

Definition byte_of_bits bits :=
  match bits with
  | [h; g; f; e;  d; c; b; a] => Ascii a b c d  e f g h
  | _ => Ascii.zero (*DUMMY*)
  end.

Lemma byte_of_bits_of_byte: forall byte: ascii, byte_of_bits(bits_of_byte byte) = byte.
Proof.
 now destruct byte.
Qed.

Lemma bits_of_byte_length : forall byte, length (bits_of_byte byte) = byte_size.
Proof.
 now destruct byte.
Qed.
