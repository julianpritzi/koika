(*! Equations showing how to implement functions on structures and arrays as bitfuns !*)
Require Import Koika.Primitives.
Import BitFuns.
Require Import Lia.

Ltac min_t :=
  repeat match goal with
         | [ |- context[Nat.min ?x ?y] ] =>
           first [rewrite (Nat.min_l x y) by min_t | rewrite (Nat.min_r x y) by min_t ]
         | _ => lia
         end.

Lemma slice_end :
  forall sz sz' (v : bits (sz + sz')),
    Bits.slice sz sz' v = vect_skipn_plus sz v.
Proof.
  intros.
  apply vect_to_list_inj.
  unfold Bits.slice, vect_skipn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  min_t; rewrite Nat.sub_diag by lia; cbn.
  rewrite app_nil_r.
  rewrite firstn_skipn.
  rewrite firstn_all2 by (rewrite vect_to_list_length; reflexivity).
  reflexivity.
Qed.

Lemma slice_front :
  forall n sz (v: bits (n + sz)) offset width,
    offset + width <= n ->
    Bits.slice offset width v =
    Bits.slice offset width (vect_firstn_plus n v).
Proof.
  intros.
  apply vect_to_list_inj.
  unfold Bits.slice, vect_extend_end_firstn, vect_extend_end, vect_firstn_plus.
  autorewrite with vect_to_list.
  rewrite skipn_firstn, firstn_firstn.
  min_t; reflexivity.
Qed.

Lemma struct_slice_correct_le :
  forall fields idx,
    struct_fields_sz (skipn (S (index_to_nat idx)) fields) + type_sz (snd (List_nth fields idx)) <=
    struct_fields_sz fields.
Proof.
  intros.
  change (type_sz (snd (List_nth fields idx))) with (struct_fields_sz [List_nth fields idx]).
  rewrite Nat.add_comm; setoid_rewrite <- list_sum_app; rewrite <- map_app; cbn [List.app].
  rewrite List_nth_skipn_cons_next.
  rewrite <- skipn_map.
  apply list_sum_skipn_le.
Qed.

Lemma array_slice_correct_le :
  forall n n' sz,
    n' < n ->
    Bits.rmul (n - S n') sz + sz <= Bits.rmul n sz.
Proof.
  intros.
  rewrite !Bits.rmul_correct.
  rewrite <- Nat.mul_succ_l.
  auto using Nat.mul_le_mono_r with arith.
Qed.

Lemma slice_subst_end :
  forall sz0 sz (bs0: bits (sz0 + sz)) (bs: bits sz),
    Bits.slice_subst sz0 sz bs0 bs = Bits.app bs (fst (Bits.split bs0)).
Proof.
  unfold Bits.split; intros; rewrite vect_split_firstn_skipn; cbn.
  apply vect_to_list_inj.
  unfold Bits.slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  replace (sz0 + sz - sz0) with (sz) by (rewrite Nat.add_comm, Nat.add_sub; reflexivity).
  rewrite vect_to_list_length, Nat.sub_diag; cbn.
  rewrite firstn_firstn by lia; min_t.
  rewrite (firstn_all2 (n := sz)) by (rewrite vect_to_list_length; lia).
  rewrite app_nil_r; reflexivity.
Qed.

Lemma slice_subst_front :
  forall sz0 sz width (bs0: bits (sz0 + sz)) (bs: bits width) offset,
    offset + width <= sz0 ->
    Bits.slice_subst offset width bs0 bs =
    Bits.app (vect_skipn_plus sz0 bs0) (Bits.slice_subst offset width (vect_firstn_plus sz0 bs0) bs).
Proof.
  clear.
  intros.
  apply vect_to_list_inj;
    unfold Bits.slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite vect_to_list_length; cbn.
  rewrite !firstn_firstn; repeat min_t.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite <- !app_assoc.
  rewrite skipn_firstn, firstn_firstn.
  min_t.
  rewrite !(firstn_all2 (vect_to_list bs)) by (rewrite vect_to_list_length; lia).
  replace (sz0 + sz - offset - width) with (sz0 + sz - (offset + width)) by lia.
  replace (sz0 - offset - width) with (sz0 - (offset + width)) by lia.
  rewrite <- !skipn_firstn.
  rewrite (firstn_all2 (n := sz0 + sz)) by (rewrite vect_to_list_length; lia).
  rewrite <- skipn_app by (rewrite firstn_length, vect_to_list_length; min_t; lia).
  rewrite List.firstn_skipn.
  reflexivity.
Qed.

Ltac _eq_t :=
  unfold _eq, _neq, beq_dec;
    intros; repeat destruct eq_dec;
      try match goal with
          | [ H: bits_of_value _ = bits_of_value _ |- _ ] => apply bits_of_value_inj in H
          end; subst; congruence.

Lemma _eq_of_value:
  forall {tau: type} {EQ: EqDec tau} (a1 a2: tau),
    _eq (bits_of_value a1) (bits_of_value a2) =
    _eq a1 a2.
Proof. _eq_t. Qed.

Lemma _neq_of_value:
  forall {tau: type} {EQ: EqDec tau} (a1 a2: tau),
    _neq (bits_of_value a1) (bits_of_value a2) =
    _neq a1 a2.
Proof. _eq_t. Qed.

Lemma get_field_bits_slice:
  forall {sig} (idx : struct_index sig) (a : type_denote (struct_t sig)),
    Bits.slice (field_offset_right sig idx) (field_sz sig idx) (bits_of_value a) =
    bits_of_value (get_field (struct_fields sig) a idx).
Proof.
  intro sig;
    repeat (simpl; unfold struct_index, field_type, field_sz, field_offset_right).
  induction (struct_fields sig) as [ | (nm & tau) l ]; simpl.
  * destruct idx.
  * destruct idx as [ | idx], a; cbn in *; intros.
    -- rewrite slice_end, vect_skipn_plus_app.
       reflexivity.
    -- rewrite <- IHl.
       rewrite slice_front, vect_firstn_plus_app by apply struct_slice_correct_le.
       reflexivity.
Qed.

Lemma get_element_bits_slice:
  forall (sig : array_sig) (idx : array_index sig)
    (a : vect (array_type sig) (array_len sig)),
    Bits.slice (element_offset_right sig idx) (element_sz sig)
          (Bits.appn (vect_map bits_of_value a)) =
    bits_of_value (vect_nth a idx).
Proof.
  intros sig;
    repeat (simpl; unfold array_index, element_sz, element_offset_right).
  induction (array_len sig); simpl.
  * destruct idx.
  * destruct idx as [ | idx], a; cbn in *; intros.
    -- rewrite Nat.sub_0_r, slice_end, vect_skipn_plus_app.
       reflexivity.
    -- rewrite <- IHn.
       rewrite slice_front, vect_firstn_plus_app by apply array_slice_correct_le, index_to_nat_bounded.
       reflexivity.
Qed.

Lemma subst_field_bits_slice_subst:
  forall {sig} (idx : struct_index sig) (a1 : type_denote (struct_t sig)) (a2 : field_type sig idx),
    Bits.slice_subst (field_offset_right sig idx) (field_sz sig idx) (bits_of_value a1) (bits_of_value a2) =
    bits_of_value (tau := struct_t _) (subst_field (struct_fields sig) a1 idx a2).
Proof.
  intro sig;
    repeat (simpl; unfold struct_index, field_type, field_sz, field_offset_right).
  induction (struct_fields sig) as [ | (nm & tau) l ]; simpl.
  * destruct idx.
  * destruct idx as [ | idx], a1; cbn in *; intros.
    -- rewrite slice_subst_end, vect_split_app.
       reflexivity.
    -- rewrite <- IHl.
       rewrite slice_subst_front, vect_firstn_plus_app, vect_skipn_plus_app by apply struct_slice_correct_le.
       reflexivity.
Qed.

Lemma subst_element_bits_slice_subst:
  forall (sig : array_sig) (idx : array_index sig)
    (a1 : vect (array_type sig) (array_len sig)) (a2 : array_type sig),
    Bits.slice_subst (element_offset_right sig idx) (element_sz sig)
                (Bits.appn (vect_map bits_of_value a1)) (bits_of_value a2) =
    Bits.appn (vect_map bits_of_value (vect_replace a1 idx a2)).
Proof.
  intro sig;
    repeat (simpl; unfold array_index, element_sz, element_offset_right).
  induction (array_len sig); simpl.
  * destruct 1.
  * destruct idx as [ | idx], a1; cbn in *; intros.
    -- rewrite Nat.sub_0_r, slice_subst_end, vect_split_app.
       reflexivity.
    -- rewrite <- IHn.
       rewrite slice_subst_front, vect_firstn_plus_app, vect_skipn_plus_app by apply array_slice_correct_le, index_to_nat_bounded.
       reflexivity.
Qed.

Lemma sel_msb {sz} (bs: bits sz):
  BitFuns.sel bs (Bits.of_nat (log2 sz) (pred sz)) =
  Ob~(Bits.msb bs).
Proof.
  unfold sel, Bits.to_index.
  rewrite Bits.to_nat_of_nat by eauto using pred_lt_pow2_log2.
  destruct sz.
  - reflexivity.
  - rewrite index_of_nat_largest.
    setoid_rewrite vect_last_nth; reflexivity.
Qed.

Definition le_plus_minus_r  (n m : nat) : n <= m -> n + (m - n) = m.
Proof.
  rewrite Nat.add_comm. apply Nat.sub_add.
Defined.

Definition slice_subst_impl {sz} offset {width} (a1: bits sz) (a2: bits width) :=
  match le_gt_dec offset sz with
  | left pr =>
    rew le_plus_minus_r offset sz pr in
      ((Bits.slice 0 offset a1) ++
       (match le_gt_dec width (sz - offset) with
        | left pr =>
          rew le_plus_minus_r width (sz - offset) pr in
            (a2 ++ Bits.slice (offset + width) (sz - offset - width) a1)
        | right _ => Bits.slice 0 (sz - offset) a2
        end))%vect
  | right _ => a1
  end.

Hint Unfold Bits.slice : vect_to_list.
Hint Unfold Bits.slice_subst : vect_to_list.
Hint Unfold slice_subst_impl : vect_to_list.
Hint Unfold vect_extend_end : vect_to_list.
Hint Unfold vect_extend_end_firstn : vect_to_list.

Ltac vect_to_list_t_step :=
  match goal with
  | _ => progress cbn
  | _ => progress (autounfold with vect_to_list)
  | _ => progress autorewrite with vect_to_list vect_to_list_cleanup
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | _ => repeat rewrite ?Nat.min_l, ?Nat.min_r by lia
  end.

Ltac vect_to_list_t :=
  try apply vect_to_list_inj; repeat vect_to_list_t_step.

Lemma slice_subst_impl_correct :
  forall {sz} offset {width} (a1: bits sz) (a2: bits width),
    Bits.slice_subst offset width a1 a2 =
    slice_subst_impl offset a1 a2.
Proof.
  intros; vect_to_list_t.
  - rewrite (firstn_all2 (n := sz - offset)) by (autorewrite with vect_to_list; lia).
    reflexivity.
  - rewrite (skipn_all2 (n := offset + width)) by (autorewrite with vect_to_list; lia).
    autorewrite with vect_to_list_cleanup; reflexivity.
  - rewrite (firstn_all2 (n := sz)) by (autorewrite with vect_to_list; lia).
    reflexivity.
Qed.

Lemma slice_full {sz}:
  forall (bs: bits sz),
    Bits.slice 0 sz bs = bs.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz)) by (autorewrite with vect_to_list; lia);
    reflexivity.
Qed.

Lemma slice_concat_l {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    Bits.slice 0 sz1 (bs1 ++ bs2)%vect = bs1.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz1)) by (autorewrite with vect_to_list; lia);
    reflexivity.
Qed.

Lemma slice_concat_r {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    Bits.slice sz1 sz2 (bs1 ++ bs2)%vect = bs2.
Proof.
  intros; vect_to_list_t.
  rewrite (skipn_all2 (n := sz1)) by (autorewrite with vect_to_list; lia).
  vect_to_list_t.
  rewrite (firstn_all2 (n := sz2)) by (autorewrite with vect_to_list; lia).
  reflexivity.
Qed.

Module Import BitProperties.
  (* Bits.single on a vector of length 1 *)
  Lemma single_1_id (b : bits 1) :
    Bits.cons (Bits.single b) Bits.nil = b.
  Proof. now destruct b, vhd, vtl. Qed.

  Lemma zeroes_snoc_idemp {sz} :
    Bits.snoc false (Bits.zeroes sz) = Bits.zeroes (S sz).
  Proof.
    induction sz; try reflexivity.
    cbn. now f_equal.
  Qed.

  Lemma msb_cons {sz bit} {b : bits (S sz)} :
    Bits.msb (Bits.cons bit b) = Bits.msb b.
  Proof. reflexivity. Qed.

  Lemma bits_msb_zeroes {sz} :
    Bits.msb (Bits.zeroes sz) = false.
  Proof.
    induction sz as [|sz' IH]; try reflexivity.
    simpl (Bits.zeroes _).
    destruct sz'; try reflexivity.
    now rewrite msb_cons.
  Qed.

  Lemma zeroes_cons_idemp {sz} :
    Bits.cons false (Bits.zeroes sz) = Bits.zeroes (S sz).
  Proof. reflexivity. Qed.

  Lemma zeroes_snoc_cons {sz} :
    Bits.snoc false (Bits.zeroes sz) = Bits.cons false (Bits.zeroes sz).
  Proof. induction sz as [| sz H]; try reflexivity; cbn; now f_equal. Qed.

  Lemma ones_snoc_idemp {sz} :
    Bits.snoc true (Bits.ones sz) = Bits.ones (S sz).
  Proof. induction sz; try reflexivity; cbn; now f_equal. Qed.

  Lemma ones_cons_idemp {sz} :
    Bits.cons true (Bits.ones sz) = Bits.ones (S sz).
  Proof. reflexivity. Qed.

  Lemma ones_snoc_cons {sz} :
    Bits.snoc true (Bits.ones sz) = Bits.cons true (Bits.ones sz).
  Proof. induction sz as [| sz H]; try reflexivity; cbn; now f_equal. Qed.

  Lemma snoc_cons_assoc {sz} bit1 bit2 (b : bits sz) :
    Bits.snoc bit1 (Bits.cons bit2 b) = Bits.cons bit2 (Bits.snoc bit1 b).
  Proof. reflexivity. Qed.

  Lemma unsnoc_uncons_assoc {sz} (b : bits (S (S sz))) :
    Bits.unsnoc (Bits.uncons b) = Bits.uncons (Bits.unsnoc b).
  Proof. reflexivity. Qed.

  Lemma unsnoc_snoc_id {sz bit} (b : bits sz) :
    Bits.unsnoc (Bits.snoc bit b) = b.
  Proof. induction sz as [|? IH]; [destruct b |cbn; rewrite IH]; easy. Qed.

  Lemma snoc_unsnoc_id {sz} (b : bits (S sz)) :
    Bits.snoc (Bits.msb b) (Bits.unsnoc b) = b.
  Proof. induction sz; apply single_1_id + cbn in *; now rewrite IHsz. Qed.

  Lemma uncons_cons_id {sz} bit (b : bits sz) :
    Bits.uncons (Bits.cons bit b) = b.
  Proof. reflexivity. Qed.

  Lemma cons_uncons_id {sz} (b : bits (S sz)) :
    Bits.cons (Bits.lsb b) (Bits.uncons b) = b.
  Proof. reflexivity. Qed.


  Lemma lsr1_uncons_snoc {sz} (b : bits sz) :
    Bits.lsr1 b = Bits.uncons (Bits.snoc false b).
  Proof. now destruct sz, b. Qed.

  Lemma lsr1_cons {sz} bit (b : bits sz) :
    Bits.lsr1 (Bits.cons bit b) = Bits.snoc false b.
  Proof. reflexivity. Qed.

  Lemma lsl1_unsnoc_cons {sz} (b : bits sz) :
    Bits.lsl1 b = Bits.unsnoc (Bits.cons false b).
  Proof. now destruct sz. Qed.

  Lemma lsl1_snoc {sz} bit (b : bits sz) :
    Bits.lsl1 (Bits.snoc bit b) = Bits.cons false b.
  Proof. now rewrite lsl1_unsnoc_cons,
    <- snoc_cons_assoc, unsnoc_snoc_id. Qed.

  Lemma lsl1_lsr1_id {sz} (b : bits sz) :
    Bits.msb b = false ->
    Bits.lsr1 (Bits.lsl1 b) = b.
  Proof. destruct sz. reflexivity.
    intro H. rewrite lsl1_unsnoc_cons, lsr1_uncons_snoc.
    erewrite <- H, <- msb_cons at 1.
    now rewrite snoc_unsnoc_id, uncons_cons_id.
  Qed.

End BitProperties.

(* making the morphism parameter implicit - enables this principle to
  be used with `induction ... using ...` *)
Local Notation nat_pair_induction := (fun A => Nat.pair_induction A _).
Local Notation N_pair_induction := (fun A => N.pair_induction A _).

Lemma nat_S_S_mod_2 n :
  S (S n) mod 2 = n mod 2.
Proof.
  erewrite <- (Nat.Div0.mod_add n 1 _).
  simpl (n + 1 * 2).
  now rewrite ?Nat.add_succ_r, Nat.add_0_r.
Qed.

Lemma nat_add_lt_pow2 n1 n2 sz :
  n1 <= 2 ^ sz ->
  n2 < 2 ^ sz ->
  n1 + n2 < 2 ^ (S sz).
Proof.
  intros [H1 | ->]%Nat.lt_eq_cases H2; cbn; rewrite Nat.add_0_r.
  rewrite (Nat.add_lt_mono_l _ _ n1) in H2.
  apply (Nat.lt_trans _ _ _ H2), Nat.add_lt_mono_r, H1.
  now apply Nat.add_lt_mono_l.
Qed.

Lemma N_add_lt_pow2 n1 n2 sz :
 (n1 <= 2 ^ sz ->
  n2 < 2 ^ sz ->
  n1 + n2 < 2 ^ (N.succ sz))%N.
Proof.
  rewrite <- (N2Nat.id n1), <- (N2Nat.id n2), <- (N2Nat.id sz), <- (N2Nat.id 2).
  rewrite <- Nat2N.inj_succ, <- ?Nat2N.inj_pow, <- ?Nat2N.inj_add, <- ?N.compare_lt_iff, <- ?N.compare_le_iff, <- ?Nat2N.inj_compare.
  rewrite ?Nat.compare_lt_iff, Nat.compare_le_iff. apply nat_add_lt_pow2.
Qed.

Lemma nat_mod_mod_mul n a b :
  (n mod (a * b)) mod a = n mod a.
Proof. now rewrite Nat.Div0.mod_mul_r, Nat.mul_comm, Nat.Div0.mod_add, Nat.Div0.mod_mod. Qed.

Lemma N_mod_mod_mul n a b :
  ((n mod (a * b)) mod a = n mod a)%N.
Proof. now rewrite N.Div0.mod_mul_r, N.mul_comm, N.Div0.mod_add, N.Div0.mod_mod. Qed.

Lemma nat_mod_mod_pow n p p':
  p <= p' ->
  (n mod 2^p') mod 2^p = n mod 2^p.
Proof. intros. now rewrite <- (Nat.sub_add _ _ H),
  Nat.pow_add_r, Nat.mul_comm, nat_mod_mod_mul. Qed.

Lemma N_mod_mod_pow n p p':
  (p <= p' ->
  (n mod 2^p') mod 2^p = n mod 2^p)%N.
Proof. intros. now rewrite <- (N.sub_add _ _ H),
  N.pow_add_r, N.mul_comm, N_mod_mod_mul. Qed.

Lemma nat_mod_div n a b :
  n mod (a * b) / b = (n / b) mod a.
Proof. destruct (Nat.eq_dec b 0); subst. now rewrite  Nat.Div0.mod_0_l.
  rewrite Nat.mul_comm, Nat.Div0.mod_mul_r, Nat.mul_comm, Nat.div_add, Nat.div_small; try easy.
  now apply Nat.mod_upper_bound. Qed.

Lemma N_mod_div n a b :
  (n mod (a * b) / b = (n / b) mod a)%N.
Proof. destruct (N.eq_dec b 0); subst. now rewrite ?N.div_0_r, N.Div0.mod_0_l.
  rewrite N.mul_comm, N.Div0.mod_mul_r, N.mul_comm, N.div_add, N.div_small; try easy.
  now apply N.mod_upper_bound. Qed.

Module Import Bits_NatN.

  Lemma to_Nat_to_N {sz} (b : bits sz) :
    Bits.to_nat b = N.to_nat (Bits.to_N b).
  Proof. reflexivity. Qed.

  Lemma to_N_to_Nat {sz} (b : bits sz) :
    Bits.to_N b = N.of_nat (Bits.to_nat b).
  Proof. unfold Bits.to_nat; now rewrite N2Nat.id. Qed.

  Lemma of_Nat_of_N sz n :
    Bits.of_nat sz n = Bits.of_N sz (N.of_nat n).
  Proof. reflexivity. Qed.

  Lemma of_N_of_Nat sz n :
    Bits.of_N sz n = Bits.of_nat sz (N.to_nat n).
  Proof. unfold Bits.of_nat; now rewrite N2Nat.id. Qed.

End Bits_NatN.

(* ========================================================================= *)
(*                          Conversions: N <-> bits                          *)
(* ========================================================================= *)

Module Bits2N.
  Open Scope N_scope.

  Lemma id_mod sz n :
    Bits.to_N (Bits.of_N sz n) = n mod 2^(N.of_nat sz).
  Proof. apply Bits.to_N_of_N_mod. Qed.

  Lemma mod_idemp {sz} (b : bits sz) :
    Bits.to_N b mod 2^(N.of_nat sz) = Bits.to_N b.
  Proof. now rewrite <- id_mod, Bits.of_N_to_N. Qed.

  Lemma id_lt_iff sz n :
    n < 2^(N.of_nat sz) <->
    Bits.to_N (Bits.of_N sz n) = n.
  Proof. split; rewrite id_mod;
    now apply N.mod_small_iff, N.pow_nonzero. Qed.

  Lemma id_lt {sz} n :
    n < 2^(N.of_nat sz) ->
    Bits.to_N (Bits.of_N sz n) = n.
  Proof. apply id_lt_iff. Qed.

  Lemma inj {sz} (b b' : bits sz) :
    Bits.to_N b = Bits.to_N b' ->
    b = b'.
  Proof.
    intro H; rewrite <- (Bits.of_N_to_N _ b), <- (Bits.of_N_to_N _ b'); now f_equal.
  Qed.

  Lemma inj_iff {sz} (b b' : bits sz) :
    Bits.to_N b = Bits.to_N b' <->
    b = b'.
  Proof. split; [apply inj|]. now destruct 1. Qed.

  Lemma inj_cons {sz} bit (b : bits sz) :
    Bits.to_N (Bits.cons bit b) = Bits.to_N b * 2 + N.b2n bit.
  Proof. now rewrite Bits.to_N_cons, N.mul_comm, N.add_comm, N.add_cancel_l. Qed.

  Lemma inj_cons_false {sz} (b : bits sz) :
    Bits.to_N (Bits.cons false b) = Bits.to_N b * 2.
  Proof. now rewrite inj_cons, N.add_0_r. Qed.

  Lemma inj_cons_true {sz} (b : bits sz) :
    Bits.to_N (Bits.cons true b) = Bits.to_N b * 2 + 1.
  Proof. now rewrite inj_cons. Qed.

  Lemma inj_snoc {sz} bit (b : bits sz) :
    Bits.to_N (Bits.snoc bit b) = Bits.to_N b + N.b2n bit * 2 ^ (N.of_nat sz).
  Proof. induction sz; try now destruct bit.
    destruct b; simpl (Bits.snoc _ _); fold (Bits.cons vhd vtl).
    rewrite ?inj_cons, IHsz, Nat2N.inj_succ, N.pow_succ_r'; lia.
  Qed.

  Lemma inj_snoc_true {sz} (b : bits sz) :
    Bits.to_N (Bits.snoc true b) = Bits.to_N b + 2 ^ (N.of_nat sz).
  Proof. rewrite inj_snoc; simpl(N.b2n _); lia. Qed.

  Lemma inj_snoc_false {sz} (b : bits sz) :
    Bits.to_N (Bits.snoc false b) = Bits.to_N b.
  Proof. rewrite inj_snoc; simpl(N.b2n _); lia. Qed.

  Lemma inj_uncons {sz} (b : bits (S sz)) :
    Bits.to_N (Bits.uncons b) = (Bits.to_N b) / 2.
  Proof. rewrite <- (cons_uncons_id b) at 2.
    rewrite inj_cons, N.div_add_l, N.b2n_div2; lia.
  Qed.

  Lemma inj_unsnoc {sz} (b : bits (S sz)) :
    Bits.to_N (Bits.unsnoc b) = (Bits.to_N b) mod 2 ^ (N.of_nat sz).
  Proof. rewrite <- (snoc_unsnoc_id b) at 2.
    now rewrite inj_snoc, <- N.Div0.add_mod_idemp_r, N.Div0.mod_mul,
      N.add_0_r, <- id_mod, Bits.of_N_to_N.
  Qed.

  Lemma inj_add_mod {sz} (b1 b2 : bits sz) :
    Bits.to_N (b1 +b b2) = (Bits.to_N b1 + Bits.to_N b2) mod 2 ^ (N.of_nat sz).
  Proof. unfold Bits.plus; now rewrite id_mod. Qed.

  Lemma inj_add_lt {sz} (b1 b2 : bits sz) :
    Bits.to_N b1 + Bits.to_N b2 < 2 ^ N.of_nat sz ->
    Bits.to_N (b1 +b b2) = (Bits.to_N b1 + Bits.to_N b2).
  Proof. intros; unfold Bits.plus; now rewrite id_lt. Qed.

  Lemma inj_lsr1 {sz} (b : bits sz) :
    Bits.to_N (Bits.lsr1 b) = (Bits.to_N b) / 2.
  Proof. now rewrite lsr1_uncons_snoc, inj_uncons, inj_snoc_false. Qed.

  Lemma inj_lsr_shiftr {sz} n (b : bits sz) :
    Bits.to_N (Bits.lsr n b) = N.shiftr (Bits.to_N b) (N.of_nat n).
  Proof. induction n as [|? IH] in b |- *. reflexivity.
    change (Bits.lsr _ _) with (Bits.lsr n (Bits.lsr1 b)).
    now rewrite IH, inj_lsr1, <- N.div2_div, N.div2_spec,
      N.shiftr_shiftr, Nat2N.inj_succ, N.add_1_l. Qed.

  Lemma inj_lsr_pow2 {sz} n (b : bits sz) :
    Bits.to_N (Bits.lsr n b) = ((Bits.to_N b) / 2^(N.of_nat n)).
  Proof. now rewrite inj_lsr_shiftr, N.shiftr_div_pow2. Qed.

  Lemma inj_lsl1 {sz} (b : bits sz) :
    Bits.to_N (Bits.lsl1 b) = (Bits.to_N b) * 2 mod 2 ^ (N.of_nat sz).
  Proof. now rewrite lsl1_unsnoc_cons, inj_unsnoc, inj_cons_false. Qed.

  Lemma inj_lsl_shiftl {sz} n (b : bits sz) :
    Bits.to_N (Bits.lsl n b) = N.shiftl (Bits.to_N b) (N.of_nat n) mod 2 ^ (N.of_nat sz).
  Proof. induction n as [|? IH] in b |- *. now rewrite N.shiftl_0_r, mod_idemp.
    change (Bits.lsl _ _) with (Bits.lsl n (Bits.lsl1 b)).
    now rewrite IH, inj_lsl1, ?N.shiftl_mul_pow2, N.Div0.mul_mod_idemp_l,
      Nat2N.inj_succ, N.pow_succ_r', N.mul_assoc. Qed.

  Lemma inj_lsl_pow2 {sz} n (b : bits sz) :
    Bits.to_N (Bits.lsl n b) = ((Bits.to_N b) * 2 ^ (N.of_nat n)) mod 2 ^ (N.of_nat sz).
  Proof. now rewrite inj_lsl_shiftl, N.shiftl_mul_pow2. Qed.
End Bits2N.

Module N2Bits.
  Open Scope N_scope.

  Lemma id {sz} (b : bits sz) :
    Bits.of_N sz (Bits.to_N b) = b.
  Proof. apply Bits.of_N_to_N. Qed.

  Lemma mod_2_idemp sz n :
    Bits.of_N sz n = Bits.of_N sz (n mod 2^(N.of_nat sz)).
  Proof. now rewrite <- Bits2N.id_mod, id. Qed.

  Lemma inj sz n n' :
    Bits.of_N sz n = Bits.of_N sz n' ->
    n mod 2^(N.of_nat sz) = n' mod 2^(N.of_nat sz).
  Proof.
    intro H. rewrite <- (Bits.to_N_of_N_mod n _), <- (Bits.to_N_of_N_mod n' _); now f_equal.
  Qed.

  Lemma inj_iff sz n n' :
    Bits.of_N sz n = Bits.of_N sz n' <->
    n mod 2^(N.of_nat sz) = n' mod 2^(N.of_nat sz).
  Proof. split; [apply inj|]. now rewrite <- ?Bits.to_N_of_N_mod, Bits2N.inj_iff. Qed.

  Lemma id' {sz} n (b : bits sz):
    b = Bits.of_N sz n <->
    Bits.to_N b = n mod 2^(N.of_nat sz).
  Proof. split. intros ->; apply Bits2N.id_mod.
    intro; now rewrite <- (id b), inj_iff, Bits2N.mod_idemp. Qed.

  Lemma inj_ult {sz n n'} :
    n < 2 ^ (N.of_nat sz) -> n' < 2 ^ (N.of_nat sz) ->
    (Bits.of_N sz n <?b Bits.of_N sz n') = (n <? n').
  Proof. intros Hn Hn'.
    unfold Bits.unsigned_lt, Bits.lift_comparison.
    now rewrite ?Bits2N.id_lt, N.ltb_compare. Qed.

  Lemma inj_ule {sz n n'} :
    n < 2 ^ (N.of_nat sz) -> n' < 2 ^ (N.of_nat sz) ->
    (Bits.of_N sz n <=?b Bits.of_N sz n') = (n <=? n').
  Proof. intros Hn Hn'. unfold Bits.unsigned_le, Bits.lift_comparison.
    rewrite ?Bits2N.id_lt, N.leb_compare;
      now destruct (n ?= n'). Qed.

  Lemma inj_ugt {sz n n'} :
    n < 2 ^ (N.of_nat sz) -> n' < 2 ^ (N.of_nat sz) ->
    (Bits.of_N sz n >?b Bits.of_N sz n') = (n' <? n).
  Proof. intros Hn Hn'. unfold Bits.unsigned_gt, Bits.lift_comparison.
    rewrite ?Bits2N.id_lt, N.ltb_compare, N.compare_antisym;
      now destruct (n' ?= n). Qed.

  Lemma inj_uge {sz n n'} :
    n < 2 ^ (N.of_nat sz) -> n' < 2 ^ (N.of_nat sz) ->
    (Bits.of_N sz n >=?b Bits.of_N sz n') = (n' <=? n).
  Proof. intros Hn Hn'. unfold Bits.unsigned_ge, Bits.lift_comparison.
    rewrite ?Bits2N.id_lt, N.leb_compare, N.compare_antisym;
      now destruct (n' ?= n). Qed.

  Lemma inj_unsnoc sz n :
    Bits.unsnoc (Bits.of_N (S sz) n) = Bits.of_N sz n.
  Proof. rewrite id', Bits2N.inj_unsnoc,
    Bits2N.id_mod, N_mod_mod_pow; lia. Qed.

  Lemma inj_0 sz :
    Bits.of_N sz 0 = Bits.zero.
  Proof. reflexivity. Qed.

  Lemma inj_0_zeroes {sz} :
    Bits.of_N sz 0 = Bits.zeroes sz.
  Proof. reflexivity. Qed.

  Lemma inj_sz_0 {n} :
    Bits.of_N 0 n = Bits.nil.
  Proof. now destruct n. Qed.

  Lemma inj_add sz n n' :
    Bits.of_N sz (n + n') = (Bits.of_N sz n) +b (Bits.of_N sz n').
  Proof. unfold Bits.plus.
    apply inj_iff; rewrite ?Bits2N.id_mod.
    apply N.Div0.add_mod. Qed.

  Lemma inj_double {sz n} :
    Bits.of_N (S sz) (N.double n) = Bits.cons false (Bits.of_N sz n).
  Proof. now destruct n. Qed.

  Lemma inj_succ_double {sz n} :
    Bits.of_N (S sz) (N.succ_double n) = Bits.cons true (Bits.of_N sz n).
  Proof. now destruct n. Qed.

  Lemma inj_half {sz n} :
    Bits.of_N sz (n / 2) = Bits.uncons (Bits.of_N (S sz) n).
  Proof.
    induction n using N.binary_ind in sz |- *; try reflexivity.
    - now rewrite inj_double, Bits.N_double_div_2, uncons_cons_id.
    - now rewrite inj_succ_double, N.succ_double_spec,
      N.mul_comm, N.div_add_l, uncons_cons_id, N.add_0_r.
  Qed.
  (* Lemma inj_sub_N sz n n' :
    Bits.of_N sz (n - n') = (Bits.of_N sz n) -b (Bits.of_N sz n').
  Proof.
    unfold Bits.minus.
  Qed. *)

  Lemma hd_succ_neg_idemp {sz n} :
    Bits.hd (Bits.of_N (S sz) n) = negb (Bits.hd (Bits.of_N (S sz) (N.succ n))).
  Proof. destruct n; now try induction p. Qed.

  Lemma hd_succ_succ_idemp {sz n} :
    Bits.hd (Bits.of_N (S sz) n) =
    Bits.hd (Bits.of_N (S sz) (N.succ (N.succ n))).
  Proof. do 2 rewrite hd_succ_neg_idemp; apply negb_involutive. Qed.

  Lemma hd_odd {sz n} :
    Bits.hd (Bits.of_N (S sz) n) = N.odd n.
  Proof. induction n using N_pair_induction;
    now try rewrite <- hd_succ_succ_idemp, N.odd_succ_succ. Qed.
End N2Bits.

(* ========================================================================= *)
(*                         Conversions: nat <-> bits                         *)
(* ========================================================================= *)

Ltac N2Nat :=
  repeat lazymatch goal with
  | |- context[N.to_nat (_ + _)] => rewrite N2Nat.inj_add
  | |- context[N.to_nat (_ - _)] => rewrite N2Nat.inj_sub
  | |- context[N.to_nat (_ * _)] => rewrite N2Nat.inj_mul
  | |- context[N.to_nat (_ / _)] => rewrite N2Nat.inj_div
  | |- context[N.to_nat (_ ^ _)] => rewrite N2Nat.inj_pow
  | |- context[N.to_nat (_ mod _)] => rewrite N2Nat.inj_mod
  | |- context[N.to_nat (N.of_nat _)] => rewrite Nat2N.id
  end.

(* declared here for scoping purposes - please use `Nat2Bits.id` instead *)
Local Lemma bits_of_nat_to_nat sz (b : bits sz) :
  Bits.of_nat sz (Bits.to_nat b) = b.
Proof.
  unfold Bits.of_nat, Bits.to_nat.
  rewrite N2Nat.id; apply N2Bits.id.
Qed.

Module Bits2Nat.
  Lemma id_mod sz n :
    Bits.to_nat (Bits.of_nat sz n) = n mod 2^sz.
  Proof. rewrite to_Nat_to_N, of_Nat_of_N, Bits.to_N_of_N_mod.
    now N2Nat. Qed.

  Lemma mod_idemp {sz} (b : bits sz) :
    Bits.to_nat b mod 2^sz = Bits.to_nat b.
  Proof. now rewrite <- id_mod, bits_of_nat_to_nat. Qed.

  Lemma id_lt_iff sz n :
    n < 2 ^ sz <->
    Bits.to_nat (Bits.of_nat sz n) = n.
  Proof. split; rewrite id_mod;
    now apply Nat.mod_small_iff, Nat.pow_nonzero. Qed.

  Lemma id_lt sz n :
    n < 2 ^ sz ->
    Bits.to_nat (Bits.of_nat sz n) = n.
  Proof. apply id_lt_iff. Qed.

  Lemma inj_iff sz (b b' : bits sz) :
    Bits.to_nat b = Bits.to_nat b' <->
    b = b'.
  Proof. now rewrite ?to_Nat_to_N, N2Nat.inj_iff, Bits2N.inj_iff. Qed.

  Lemma inj sz (b b' : bits sz) :
    Bits.to_nat b = Bits.to_nat b' ->
    b = b'.
  Proof. apply inj_iff. Qed.

  Lemma inj_cons {sz} bit (b : bits sz) :
    Bits.to_nat (Bits.cons bit b) = Bits.to_nat b * 2 + Nat.b2n bit.
  Proof. rewrite to_Nat_to_N, Bits2N.inj_cons. N2Nat.
    now destruct bit. Qed.

  Lemma inj_cons_false {sz} (b : bits sz) :
    Bits.to_nat (Bits.cons false b) = Bits.to_nat b * 2.
  Proof. now rewrite inj_cons, Nat.add_0_r. Qed.

  Lemma inj_cons_true {sz} (b : bits sz) :
    Bits.to_nat (Bits.cons true b) = Bits.to_nat b * 2 + 1.
  Proof. now rewrite inj_cons. Qed.

  Lemma inj_snoc {sz} bit (b : bits sz) :
    Bits.to_nat (Bits.snoc bit b) = Bits.to_nat b + Nat.b2n bit * 2^sz.
  Proof. rewrite to_Nat_to_N, Bits2N.inj_snoc. N2Nat. now destruct bit. Qed.

  Lemma inj_snoc_true {sz} (b : bits sz) :
    Bits.to_nat (Bits.snoc true b) = Bits.to_nat b + 2^sz.
  Proof. rewrite inj_snoc; simpl(Nat.b2n _); lia. Qed.

  Lemma inj_snoc_false {sz} (b : bits sz) :
    Bits.to_nat (Bits.snoc false b) = Bits.to_nat b.
  Proof. rewrite inj_snoc; simpl(Nat.b2n _); lia. Qed.

  Lemma inj_uncons {sz} (b : bits (S sz)) :
    Bits.to_nat (Bits.uncons b) = (Bits.to_nat b) / 2.
  Proof. rewrite to_Nat_to_N, Bits2N.inj_uncons. now N2Nat. Qed.

  Lemma inj_unsnoc {sz} (b : bits (S sz)) :
    Bits.to_nat (Bits.unsnoc b) = (Bits.to_nat b) mod 2^sz.
  Proof. rewrite to_Nat_to_N, Bits2N.inj_unsnoc. now N2Nat. Qed.

  Lemma inj_add_mod {sz} (b1 b2 : bits sz) :
    Bits.to_nat (b1 +b b2) = (Bits.to_nat b1 + Bits.to_nat b2) mod 2^sz.
  Proof. rewrite to_Nat_to_N, Bits2N.inj_add_mod. now N2Nat. Qed.

  Lemma inj_add_lt {sz} (b1 b2 : bits sz) :
    Bits.to_nat b1 + Bits.to_nat b2 < 2^sz ->
    Bits.to_nat (b1 +b b2) = (Bits.to_nat b1 + Bits.to_nat b2).
  Proof. intros; unfold Bits.plus;
    now rewrite of_N_of_Nat, ?to_N_to_Nat, <- Nat2N.inj_add, Nat2N.id, id_lt. Qed.

  Lemma inj_lsr1 {sz} (b : bits sz) :
    Bits.to_nat (Bits.lsr1 b) = (Bits.to_nat b) / 2.
  Proof. now rewrite lsr1_uncons_snoc, inj_uncons, inj_snoc_false. Qed.

  Lemma inj_lsr_shiftr {sz} n (b : bits sz) :
    Bits.to_nat (Bits.lsr n b) = Nat.shiftr (Bits.to_nat b) n.
  Proof. induction n as [|? IH] in b |- *. reflexivity.
    change (Bits.lsr _ _) with (Bits.lsr n (Bits.lsr1 b)).
    now rewrite IH, inj_lsr1, <- Nat.div2_div, Nat.div2_spec,
      Nat.shiftr_shiftr, Nat.add_1_l. Qed.

  Lemma inj_lsr_pow2 {sz} n (b : bits sz) :
    Bits.to_nat (Bits.lsr n b) = ((Bits.to_nat b) / 2^n).
  Proof. now rewrite inj_lsr_shiftr, Nat.shiftr_div_pow2. Qed.

  Lemma inj_lsl1 {sz} (b : bits sz) :
    Bits.to_nat (Bits.lsl1 b) = (Bits.to_nat b) * 2 mod 2^sz.
  Proof. now rewrite lsl1_unsnoc_cons, inj_unsnoc, inj_cons_false. Qed.

  Lemma inj_lsl_shiftl {sz} n (b : bits sz) :
    Bits.to_nat (Bits.lsl n b) = Nat.shiftl (Bits.to_nat b) n mod 2^sz.
  Proof. induction n as [|? IH] in b |- *. now rewrite Nat.shiftl_0_r, mod_idemp.
    change (Bits.lsl _ _) with (Bits.lsl n (Bits.lsl1 b)).
    now rewrite IH, inj_lsl1, ?Nat.shiftl_mul_pow2, Nat.Div0.mul_mod_idemp_l,
      Nat.pow_succ_r', Nat.mul_assoc. Qed.

  Lemma inj_lsl_pow2 {sz} n (b : bits sz) :
    Bits.to_nat (Bits.lsl n b) = ((Bits.to_nat b) * 2^n) mod 2^sz.
  Proof. now rewrite inj_lsl_shiftl, Nat.shiftl_mul_pow2. Qed.
End Bits2Nat.

Module Nat2Bits.
  Open Scope nat_scope. (* TODO: remove that annoying string import *)

  Lemma id {sz} (b : bits sz) :
    Bits.of_nat sz (Bits.to_nat b) = b.
  Proof. apply bits_of_nat_to_nat. Qed.

  Lemma mod_idemp {sz} n :
    Bits.of_nat sz n = Bits.of_nat sz (n mod 2^sz).
  Proof. now rewrite <- Bits2Nat.id_mod, id. Qed.

  Lemma inj {sz} n n' :
    Bits.of_nat sz n = Bits.of_nat sz n' ->
    n mod 2^sz = n' mod 2^sz.
  Proof. intro H; rewrite <- (Bits2Nat.id_mod sz n), <- (Bits2Nat.id_mod sz n');
    now f_equal. Qed.

  Lemma inj_iff {sz} n n' :
    Bits.of_nat sz n = Bits.of_nat sz n' <->
    n mod 2^sz = n' mod 2^sz.
  Proof. split; [apply inj|].
    now rewrite <- ?Bits2Nat.id_mod, Bits2Nat.inj_iff. Qed.

  Lemma id' {sz} n (b : bits sz):
    b = Bits.of_nat sz n <->
    Bits.to_nat b = n mod 2^sz.
  Proof. split. intros ->; apply Bits2Nat.id_mod.
    intro; now rewrite <- (id b), inj_iff, Bits2Nat.mod_idemp. Qed.

  Lemma inj_ult {sz} n n' :
    n < 2 ^sz -> n' < 2 ^sz ->
    (Bits.of_nat sz n <?b Bits.of_nat sz n') = (n <? n').
  Proof. intros Hn Hn'; unfold Bits.unsigned_lt, Bits.lift_comparison.
    now rewrite ?to_N_to_Nat, ?Bits2Nat.id_lt, Nat.ltb_compare,
      N2Nat.inj_compare, ?Nat2N.id. Qed.

  Lemma inj_ule {sz} n n' :
    n < 2 ^sz -> n' < 2 ^sz ->
    (Bits.of_nat sz n <=?b Bits.of_nat sz n') = (n <=? n').
  Proof. intros Hn Hn'; unfold Bits.unsigned_le, Bits.lift_comparison.
    rewrite ?to_N_to_Nat, ?Bits2Nat.id_lt, Nat.leb_compare,
      N2Nat.inj_compare, ?Nat2N.id; now destruct (n ?= n'). Qed.

  Lemma inj_ugt {sz} n n' :
    n < 2 ^sz -> n' < 2 ^sz ->
    (Bits.of_nat sz n >?b Bits.of_nat sz n') = (n' <? n).
  Proof. intros Hn Hn'; unfold Bits.unsigned_gt, Bits.lift_comparison.
    rewrite ?to_N_to_Nat, ?Bits2Nat.id_lt, Nat.ltb_compare, N2Nat.inj_compare, ?Nat2N.id,
      Nat.compare_antisym; now destruct (n' ?= n). Qed.

  Lemma inj_uge {sz} n n' :
    n < 2 ^sz -> n' < 2 ^sz ->
    (Bits.of_nat sz n >=?b Bits.of_nat sz n') = (n' <=? n).
  Proof. intros Hn Hn'. unfold Bits.unsigned_ge, Bits.lift_comparison.
    rewrite ?to_N_to_Nat, ?Bits2Nat.id_lt, Nat.leb_compare, N2Nat.inj_compare, ?Nat2N.id,
      Nat.compare_antisym; now destruct (n' ?= n). Qed.

  Lemma inj_unsnoc {sz} n :
    Bits.unsnoc (Bits.of_nat (S sz) n) = Bits.of_nat sz n.
  Proof. rewrite id', Bits2Nat.inj_unsnoc,
    Bits2Nat.id_mod, nat_mod_mod_pow; lia. Qed.

  Lemma inj_snoc {sz} bit n :
    Bits.snoc bit (Bits.of_nat sz n) = Bits.of_nat (S sz) ((n mod 2^sz) + Nat.b2n bit * 2^sz).
  Proof. rewrite id', Bits2Nat.inj_snoc, Bits2Nat.id_mod, (Nat.mod_small _ (2 ^ S sz)); try easy.
    rewrite Nat.add_comm; apply nat_add_lt_pow2. destruct bit; cbn; lia.
    now apply Nat.mod_upper_bound, Nat.pow_nonzero. Qed.

  Lemma inj_snoc_true {sz} n :
    Bits.snoc true (Bits.of_nat sz n) = Bits.of_nat (S sz) ((n mod 2^sz) + 2^sz).
  Proof. rewrite inj_snoc. cbn. now rewrite Nat.add_0_r. Qed.

  Lemma inj_snoc_false {sz} n :
    Bits.snoc false (Bits.of_nat sz n) = Bits.of_nat (S sz) (n mod 2^sz).
  Proof. rewrite inj_snoc. cbn. now rewrite Nat.add_0_r. Qed.

  Lemma inj_uncons {sz} n :
    Bits.uncons (Bits.of_nat (S sz) n) = Bits.of_nat sz (n / 2).
  Proof. now rewrite id', Bits2Nat.inj_uncons, Bits2Nat.id_mod,
    Nat.pow_succ_r', Nat.mul_comm, nat_mod_div. Qed.

  Lemma inj_0 {sz} :
    Bits.of_nat sz 0 = Bits.zero.
  Proof. reflexivity. Qed.

  Lemma inj_0_zeroes {sz} :
    Bits.of_nat sz 0 = Bits.zeroes sz.
  Proof. reflexivity. Qed.

  Lemma inj_sz_0 n :
    Bits.of_nat 0 n = Bits.nil.
  Proof. apply N2Bits.inj_sz_0. Qed.

  Lemma inj_sz_1_odd n :
    Bits.of_nat 1 n = Bits.cons (Nat.odd n) Bits.nil.
  Proof. induction n using nat_pair_induction; try reflexivity.
    now rewrite Nat.odd_succ_succ, mod_idemp, nat_S_S_mod_2,
      <- (@mod_idemp 1). Qed.

  Lemma inj_add {sz} n n' :
    Bits.of_nat sz (n + n') = (Bits.of_nat sz n) +b (Bits.of_nat sz n').
  Proof. unfold Bits.of_nat; now rewrite <- N2Bits.inj_add,
    Nat2N.inj_add. Qed.

  Lemma inj_double {sz} n :
    Bits.of_nat (S sz) (2 * n) = Bits.cons false (Bits.of_nat sz n).
  Proof. unfold Bits.of_nat; rewrite Nat2N.inj_mul.
    destruct (N.of_nat n); reflexivity. Qed.

  Lemma inj_double_S {sz} n :
    Bits.of_nat (S sz) (S (2 * n)) = Bits.cons true (Bits.of_nat sz n).
  Proof. unfold Bits.of_nat; rewrite Nat2N.inj_succ, Nat2N.inj_mul.
    destruct (N.of_nat n); reflexivity. Qed.

  Lemma inj_half {sz} n :
    Bits.of_nat sz (n / 2) = Bits.uncons (Bits.of_nat (S sz) n).
  Proof. unfold Bits.of_nat.
    now rewrite Nat2N.inj_div, N2Bits.inj_half. Qed.

  Lemma inj_lsl1 {sz} n :
    Bits.of_nat sz (n * 2) = Bits.lsl1 (Bits.of_nat sz n).
  Proof. destruct sz. now rewrite ?inj_sz_0.
    rewrite Nat.mul_comm, inj_double; unfold Bits.lsl1;
    now rewrite inj_unsnoc. Qed.

  Lemma inj_lsl_pow2 {sz} n s :
    Bits.of_nat sz (n * 2^s) = Bits.lsl s (Bits.of_nat sz n).
  Proof. induction s in n |- *. now rewrite Nat.mul_1_r.
    change (Bits.lsl _ ?b) with (Bits.lsl s (Bits.lsl1 b));
    rewrite <- inj_lsl1, <- IHs, Nat.pow_succ_r'; f_equal; lia. Qed.

  Lemma inj_lsl_shiftl {sz} n s :
    Bits.of_nat sz (Nat.shiftl n s) = Bits.lsl s (Bits.of_nat sz n).
  Proof. now rewrite Nat.shiftl_mul_pow2, inj_lsl_pow2. Qed.

  Lemma inj_lsr1 {sz} n :
    Bits.of_nat sz ((n mod 2^sz) / 2) = Bits.lsr1 (Bits.of_nat sz n).
  Proof. destruct sz. now rewrite ?inj_sz_0.
    unfold Bits.lsr1; now rewrite inj_uncons, inj_snoc_false,
      Nat.pow_succ_r', Nat.mul_comm, nat_mod_div. Qed.

  Lemma inj_lsr_pow2 {sz} n s :
    Bits.of_nat sz ((n mod 2^sz) / 2^s) = Bits.lsr s (Bits.of_nat sz n).
  Proof. induction s in n |- *. now rewrite Nat.div_1_r, <- mod_idemp.
    change (Bits.lsr _ ?b) with (Bits.lsr s (Bits.lsr1 b)). rewrite <- inj_lsr1, <- IHs,
      <- nat_mod_div, Nat.Div0.div_div, <- Nat.pow_succ_r', (Nat.mod_small _ (_ * _)).
    reflexivity. rewrite Nat.mod_upper_bound, <- Nat.add_0_r at 1.
    replace (_ * 2) with (2^sz + 2^sz) by lia. apply Plus.plus_lt_compat_l_stt, Nat.neq_0_lt_0.
    all: apply Nat.pow_nonzero; lia. Qed.

  Lemma inj_lsr_shiftr {sz} n s :
    Bits.of_nat sz (Nat.shiftr (n mod 2^sz) s) = Bits.lsr s (Bits.of_nat sz n).
  Proof. now rewrite Nat.shiftr_div_pow2, inj_lsr_pow2. Qed.

  Lemma hd_S_neg_idemp {sz n} :
    Bits.hd (Bits.of_nat (S sz) n) = negb (Bits.hd (Bits.of_nat (S sz) (S n))).
  Proof. unfold Bits.of_nat; rewrite Nat2N.inj_succ.
    apply N2Bits.hd_succ_neg_idemp. Qed.

  Lemma hd_S_S_idemp {sz n} :
    Bits.hd (Bits.of_nat (S sz) n) =
    Bits.hd (Bits.of_nat (S sz) (S (S n))).
  Proof. do 2 rewrite hd_S_neg_idemp.
    apply negb_involutive. Qed.

  Lemma hd_odd {sz n} :
    Bits.hd (Bits.of_nat (S sz) n) = Nat.odd n.
  Proof. induction n using nat_pair_induction;
      now try rewrite <- hd_S_S_idemp. Qed.
End Nat2Bits.

Section Arithmetic.

  (* The next lemmas simplify 2 * x *)
  Arguments N.mul / !n !m.

  Lemma sel_spec :
    forall (sz: nat) (bs: bits sz) idx,
      BitFuns.sel bs idx = Ob~(N.testbit (Bits.to_N bs) (Bits.to_N idx)).
  Proof.
    intros.
    unfold BitFuns.sel.
    f_equal.
    unfold Bits.to_index.
    destruct (index_of_nat sz (Bits.to_nat idx)) eqn:Hindex.
    - rewrite <-(N2Nat.id (Bits.to_N idx)).
      fold (Bits.to_nat idx).
      remember (Bits.to_nat idx) as n_idx eqn:Hn_idx.
      clear Hn_idx idx.
      generalize dependent sz.
      induction n_idx as [| idx IH].
      + intros sz bs i Hindex. cbn.
        destruct sz; [destruct i | ].
        inversion Hindex. repeat cleanup_step.
        destruct bs. repeat cleanup_step.
        rewrite N.add_comm. fold (N.b2n vhd).
        rewrite N.testbit_0_r.
        reflexivity.
      + intros sz bs i Hindex. rewrite Nat2N.inj_succ.
        destruct sz; [destruct i | ].
        cbn in Hindex.
        destruct (index_of_nat sz idx) eqn:Hi; repeat cleanup_step.
        destruct bs. repeat cleanup_step.
        rewrite N.add_comm. fold (N.b2n vhd).
        rewrite N.testbit_succ_r.
        apply IH; auto.
    - apply index_of_nat_none_ge in Hindex.
      unfold Bits.to_nat in Hindex.
      assert (Bits.to_N idx >= N.of_nat sz)%N as Hle by lia.
      pose proof (Bits.to_N_bounded bs).
      destruct (Bits.to_N bs); [ reflexivity | ].
      symmetry. apply N.bits_above_log2.
      apply N.ge_le in Hle.
      eapply N.lt_le_trans; [ | exact Hle].
      apply N.log2_lt_pow2; lia.
  Qed.

  Lemma to_N_lsl :
    forall sz1 sz2 (x: bits sz1) (y: bits sz2),
      (Bits.to_N (BitFuns.lsl x y) =
       (Bits.to_N x * (2 ^ (Bits.to_N y))) mod (2 ^ N.of_nat sz1))%N.
  Proof.
    intros. unfold lsl.
    rewrite <-(N2Nat.id (Bits.to_N y)).
    apply Bits2N.inj_lsl_pow2.
  Qed.

  Lemma to_N_extend_end_false :
    forall sz (x: bits sz) sz', Bits.to_N (Bits.extend_end x sz' false) = Bits.to_N x.
  Proof.
    intros.
    unfold Bits.extend_end.
    rewrite Bits.to_N_rew, Bits.to_N_app, Bits.to_N_zeroes, N.mul_0_l, N.add_0_l.
    reflexivity.
  Qed.
End Arithmetic.
