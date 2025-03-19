(*! Understanding conflicts and forwarding, with modules !*)
(* Require Import Koika.Parsing. *)
Require Import Koika.Frontend.
Require Import Koika.TypedParsing.

Module Type QueueParam.
  Parameter T: type.
End QueueParam.

Module Queue (QP : QueueParam).
  Import QP.

  Inductive reg_t := empty | data.
  Definition R reg :=
    match reg with
    | empty => bits_t 1
    | data => T
    end.

  Definition dequeue0: function R empty_Sigma :=
    <{ fun dequeue0 () : T =>
         guard(!read0(empty)); write0(empty, Ob~1); read0(data) }>.

  Definition enqueue0: function R empty_Sigma :=
    <{ fun enqueue0 (val: T) : unit_t =>
         guard(read0(empty)); write0(empty, Ob~0); write0(data, val) }>.

  Definition dequeue1: function R empty_Sigma :=
    <{ fun dequeue1 () : T =>
         guard(!read1(empty)); write1(empty, Ob~1); read1(data) }>.

  Require Import Koika.Hoare.
  Require Import Koika.Environments.

  (* TODO generalize over sig *)
  Notation "'{{' P '}}' a '{{' Q '}}'" := (forall REnv, @hoare_triple _ _ _ R empty_Sigma REnv _ _ empty_sigma a P Q) (at level 10, P custom assertion, Q custom ret_assertion, only parsing).
  From Coq Require Import Utf8.


  Theorem simple_hoare_a :
    ∀ sz n: nat,
    {{ True }} (<{ a := #n }> : action' R empty_Sigma (sig := [("a", bits_t sz); ("b", bits_t sz)])) {{ Γ[a] = n }}.
  Proof.
    hoare.
  Qed.

  Theorem simple_hoare_b :
    ∀ sz n m: nat,
    {{ Γ[a] = n }} (<{ b := #m }> : action' R empty_Sigma (sig := [("a", bits_t sz); ("b", bits_t sz)])) {{ Γ[a] = n /\ Γ[b] = m }}.
  Proof.
    hoare. now split.
  Qed.
    (* rewrite cassoc_creplace_neq_k. split. assumption. reflexivity. *)
    (* easy. *)
  (* Qed. *)

  Theorem simple_hoare :
    ∀ sz n m: nat,
    {{ True }} (<{ a := #n; b := #m }> : action' R empty_Sigma (sig := [("a", bits_t sz); ("b", bits_t sz)])) {{ Γ[a] = n /\ Γ[b] = m }}.
  Proof.
    intros.
    eapply hoare_seq.
    - apply simple_hoare_b.
    - apply simple_hoare_a.
  Qed.

  Theorem queue_enc_fail :
    ∀ n,
    {{ env[empty] = 0 /\ Γ[a] = n}} (<{ enqueue0(a) }> : action' _ _ (sig := [("a", T)])) {{ False }}.
  Proof.
    intros.
    unfold delay_tau.
    hoare_step.
    hoare_step.
    eapply hoare_args_weaken_pre.
    hoare_step.
    hoare_step.
    hoare_step.
    hoare_cleanup.
    hoare_step.
    hoare.
    apply (hoare_read (R := R) _ empty).
    hoare_cleanup. cbn. unfold ret_assertion_of_assertion. rewrite H.
    cbn.
    trivial.
  Qed.

  Theorem queue_enq_correct :
    ∀ n: nat,
    {{ env[empty] = 1 /\ Γ[a] = n }} (<{ enqueue0(a) }> : action' R empty_Sigma (sig := [("a", T)])) {{ env[data] = n /\ env[empty] = 0 }}.
  Proof.
    intros.
    hoare.
    hoare.
    apply (hoare_read (R := R) _ empty).
    hoare_cleanup.
    unfold ret_assertion_of_assertion.

    rewrite get_put_eq.
    let e := eval cbn in (eq_dec data empty) in
    match e with
    | right ?Hneq => rewrite (get_put_neq _ _ _ _ _ Hneq)
    end.
    rewrite get_put_eq.
    vm_compute (var_ref _ _).
    hoare_cleanup.
    rewrite H.
    split. assumption. reflexivity.
  Qed.

  Theorem queue_deq_correct :
    ∀ n: nat,
    {{ env[data] = n /\ env[empty] = 0 }} (<{ dequeue1() }> : action' R empty_Sigma (sig := [("a", T)])) {{ r, r = n }}.
  Proof.
    intros.
    hoare.
    hoare.
    apply (hoare_read (R := R) _ data).
    apply (hoare_read (R := R) _ empty).
    hoare_cleanup.
    unfold ret_assertion_of_assertion.
    let e := eval cbn in (eq_dec empty data) in
    match e with
    | right ?Hneq => rewrite (get_put_neq _ _ _ _ _ Hneq)
    end.
    rewrite H0.
    assumption.
  Qed.


  (* Theorem queue_enc_dec : *)
    (* ∀ sz n: nat,
    ∀ sig,
    {{ env[empty] = 1 }} (<{ enqueue0(`Const (@value_of_bits T (Bits.of_nat _ n))`); dequeue1() }> : action' R empty_Sigma (sig := sig)) {{ r, r = n }}.
  Proof. *)
  Theorem queue_enc_dec:
    ∀ n: nat,
    {{ env[empty] = 1 /\ Γ[a] = n }} (<{ enqueue0(a); dequeue1() }> : action' R empty_Sigma (sig := [("a", T)])) {{ r, r = n }}.
  Proof.
    intros.
    eapply hoare_seq.
    - apply queue_deq_correct.
    - apply queue_enq_correct.
  Qed.
End Queue.

Module Type QueueParam'.
  Parameter T: type. (* type of data which is stored *)
  Parameter sz: nat. (* number of data items which can be stored *)
End QueueParam'.

Module Queue' (QP : QueueParam').
  Import QP.

  (* TODO extend to real queue *)
  (* Inductive reg_t := empty | data (idx: Vect.index sz). *)
  Inductive reg_t := empty | data.
  (* Axiom reg_t_ft : FiniteType reg_t. *)

  Definition R reg :=
    match reg with
    | empty => bits_t 1
    | data => T
    end.

  Definition dequeue0: function R empty_Sigma :=
    <{ fun dequeue0 () : T =>
         guard(!read0(empty)); write0(empty, Ob~1); read0(data) }>.

  Definition enqueue0: function R empty_Sigma :=
    <{ fun enqueue0 (val: T) : unit_t =>
         guard(read0(empty)); write0(empty, Ob~0); write0(data, val) }>.

  Definition dequeue1: function R empty_Sigma :=
    <{ fun dequeue1 () : T =>
         guard(!read1(empty)); write1(empty, Ob~1); read1(data) }>.

End Queue'.

Module QueueParam32 <: QueueParam.
  Definition T := bits_t 32.
End QueueParam32.
Module Import Queue32 := Queue QueueParam32.

Inductive reg_t :=
  | in0: Queue32.reg_t -> reg_t
  | in1: Queue32.reg_t -> reg_t
  | fifo: Queue32.reg_t -> reg_t
  | out: Queue32.reg_t -> reg_t.

Inductive rule_name_t := deq0 | deq1 | process.

Definition R (reg: reg_t) : type :=
  match reg with
  | in0 st => Queue32.R st
  | in1 st => Queue32.R st
  | fifo st => Queue32.R st
  | out st => Queue32.R st
  end.

Definition rules (rl: rule_name_t) : action R empty_Sigma :=
  match rl with
  | deq0 =>
    <{ fifo.(enqueue0)(in0.(dequeue0)()) }>
  | deq1 =>
    <{ fifo.(enqueue0)(in1.(dequeue0)()) }>
  | process =>
    <{ out.(enqueue0)(|32`d412| + fifo.(dequeue1)()) }>
  end.

(* Definition rules : rule_name_t -> rule R empty_Sigma :=
  tc_rules R empty_Sigma urules. *)

Definition pipeline : scheduler :=
  deq0 |> deq1 |> process |> done.

Definition external (r: rule_name_t) := false.

Definition r (reg: reg_t) : R reg :=
  match reg with
  | in0 empty => Ob~0
  | in0 data => Bits.of_nat _ 42
  | in1 empty => Ob~0
  | in1 data => Bits.of_nat _ 73
  | fifo empty => Ob~1
  | fifo data => Bits.zero
  | out empty => Ob~1
  | out data => Bits.zero
  end.

Definition cr := ContextEnv.(create) r.

Definition interp_result :=
  tc_compute (commit_update cr (interp_scheduler cr empty_sigma rules pipeline)).

Definition circuits :=
  compile_scheduler rules external pipeline.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r reg;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := pipeline;
                   koika_module_name := "conflicts_modular" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "conflicts_modular.ml" prog.
