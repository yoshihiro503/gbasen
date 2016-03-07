Require Import Ascii List Program Ascii.
Require Import Util ListUtil.
Require Charset.

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


Definition modulo_charsize n := modulo n C.char_size C.char_size_positive.

Definition encode bs :=
  let r := byte_size * List.length bs |> modulo_charsize in
  encode_ r bs ++ [C.of_nat r].

Definition decode (cs: list C.char) :=
  let '(cs, lastchar) := split_last C.dummy cs in
  let r := lastchar |> C.to_nat in
  decode_ r cs.

End Make.
