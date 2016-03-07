Require Import Ascii List Program Ascii.
Require Import GBaseN.Util GBaseN.ListUtil.
Require GBaseN.Charset.

Module Make(C : Charset.Sig).


Definition encode_ (r: nat) bs :=
  bs |> concat_map bits_of_byte
     |> (fun bits => bits ++ repeat false (C.char_size - r))
     |> ntake C.char_size
     |> map C.of_bits
.

Definition decode_ (r: nat) cs :=
  cs |> concat_map C.to_bits
     |> drop_right (C.char_size - r)
     |> ntake byte_size
     |> map byte_of_bits
.

Require Import Arith.Euclid.
Definition modulo_charsize (n: nat) : nat.
 destruct (modulo C.char_size C.char_size_positive n) as [r].
 exact r.
Defined.

Lemma modulo_charsize_spec : forall n, Modulo n C.char_size (modulo_charsize n).
Proof.
 intro n. unfold modulo_charsize. destruct (modulo _ _) as [r Hmod].
 destruct Hmod as [q Hmod]. exists q. destruct Hmod as [Hmod1 Hmod2]. now constructor.
Qed.

Lemma modulo_charsize_lt : forall n, modulo_charsize n < C.char_size.
Proof.
 intro n. destruct (modulo_charsize_spec n) as [q Hmod]. now destruct Hmod as [Hmod1 _].
Qed.

Definition encode bs :=
  let r := byte_size * List.length bs |> modulo_charsize in
  encode_ r bs ++ [C.of_nat r].

Definition decode (cs: list C.char) :=
  let '(cs, lastchar) := split_last C.dummy cs in
  let r := lastchar |> C.to_nat in
  decode_ r cs.

End Make.