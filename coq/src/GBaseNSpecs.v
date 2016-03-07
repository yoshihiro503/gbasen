Require Import Arith List Program.
Require Import GBaseN.Util GBaseN.ListUtil.
Require GBaseN.GBaseN.

Declare Module C : Charset.Sig.
Module GBaseN := GBaseN.Make C.

Lemma decode_encode_ : forall bs r,
  Modulo (byte_size * length bs) C.char_size r ->
  GBaseN.decode_ r (GBaseN.encode_ r bs) = bs.
Proof.
 intros bs r Hmodulo.
 unfold GBaseN.decode_, GBaseN.encode_, Util.revapply, concat_map.
 destruct Hmodulo as [q Hq]. inversion Hq as [Hmod1 Hmod2].
 rewrite List.map_map. rewrite map_id_forall.
 - rewrite concat_ntake. rewrite drop_right_append; [|now rewrite repeat_length].
   rewrite ntake_concat_rectangle; [|unfold byte_size; now auto with arith |].
   + rewrite map_map. rewrite map_id_forall; [reflexivity|].
     apply Forall_forall. intros byte _. apply byte_of_bits_of_byte.
   + apply Forall_map. apply Forall_forall. intros byte _. now rewrite bits_of_byte_length.
 - (* to_bits (of_bits x) = x の証明ここから *)
   apply Forall_forall. intro bits.
   set(bss := concat _ ++ _). intros Hin.
   apply C.to_bits_of_bits.
   set (ntake_length _ C.char_size bss). rewrite Forall_forall in f.
   apply f.
   + (* bss <> nilを証明せなあかん *)
     unfold bss. destruct bs.
     * simpl. case_eq (C.char_size - r); [omega | discriminate].
     * now destruct a.
   + unfold bss. rewrite app_length, repeat_length. 
     exists (S q). constructor; [now apply C.char_size_positive|].
     rewrite (concat_length_rectangle _ byte_size).
     * rewrite map_length, Hmod2. rewrite <-plus_assoc, <-le_plus_minus; [ring|].
       now apply lt_le_weak.
     * apply Forall_map. apply Forall_forall. intros byte _. now rewrite bits_of_byte_length.
   + assumption.
Qed.

Theorem decode_encode : forall bs,
  GBaseN.decode (GBaseN.encode bs) = bs.
Proof.
 intro bs. unfold GBaseN.decode, GBaseN.encode, Util.revapply.
 rewrite split_last_append. rewrite C.to_nat_of_nat.
 - apply decode_encode_. now apply GBaseN.modulo_charsize_spec.
 - now apply GBaseN.modulo_charsize_lt.
Qed.