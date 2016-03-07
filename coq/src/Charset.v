Module Type Sig.
Variable char : Set.

Variable char_size : nat.
Axiom char_size_positive : char_size > 0.

(* listの長さは必ずchar_sizeであること *)
Variable of_bits : list bool -> char.
(* 返すlistの長さは必ずchar_sizeとなる *)
Variable to_bits : char -> list bool.
(*Axiom of_bits_to_bits : forall char, of_bits (to_bits char) = char. 未使用 *)
Axiom to_bits_of_bits : forall bits,
  length bits = char_size -> to_bits (of_bits bits) = bits.

(* 2^char_size より小さい値を期待 *)
Variable of_nat : nat -> char.
(* 2^char_size より小さい値を返す *)
Variable to_nat : char -> nat.
(*Axiom of_nat_to_nat : forall c, of_nat (to_nat c) = c. 未使用*)
Axiom to_nat_of_nat : forall n, n < char_size -> to_nat (of_nat n) = n.

Variable dummy: char.
End Sig.