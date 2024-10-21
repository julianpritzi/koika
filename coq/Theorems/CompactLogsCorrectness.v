Require Koika.CompactLogs.
Require Koika.CompactSemantics.
Require Koika.Logs.
Require Koika.TypedSyntax.
Require Koika.TypedSemantics.
Require Import Koika.FiniteType.
Require Import Koika.Types.
Require Import Koika.Environments.

Section CompactEquality.
  Context {reg_t ext_fn_t var_t pos_t fn_name_t: Type}.
  Context {ft : FiniteType reg_t}.
  Context {tau : type}.
  Context {sig : tsig var_t}.

  Context {REnv: Env reg_t}.

  Context {R : reg_t -> type}.
  Context {sigma : (ext_fn_t -> ExternalSignature)}.

  Context {r : (forall reg : reg_t, R reg)}.

  Definition tcontext (sig: tsig var_t) :=
    context (fun k_tau => type_denote (snd k_tau)) sig.
  Context {Gamma : tcontext sig}.

  Context {a : TypedSyntax.action pos_t var_t fn_name_t R sigma sig tau}.

  Context {sigma_denote : (forall fn: ext_fn_t, Sig_denote (sigma fn))}.

  Lemma Logs_latest_write_empty :
    forall idx : reg_t,
    @Logs.latest_write _ R REnv Logs.log_empty idx = None.
  Proof.
    intros.
    unfold Logs.latest_write, Logs.log_find, Logs.log_empty.
    rewrite getenv_create.
    reflexivity.
  Defined.

  Lemma Logs_commit_update_empty :
    forall env : REnv.(env_t) R,
    Logs.commit_update env Logs.log_empty = env.
  Proof.
    intros.
    unfold Logs.commit_update.
    apply equiv_eq.
    unfold equiv.
    intros.
    rewrite getenv_create.
    rewrite Logs_latest_write_empty.
    reflexivity.
  Defined.

  Lemma CompactLogs_commit_update_empty :
    forall env : REnv.(env_t) R,
    CompactLogs.commit_update env CompactLogs.log_empty = env.
  Proof.
    intros.
    unfold CompactLogs.commit_update.
    apply equiv_eq.
    unfold equiv.
    intro.
    rewrite getenv_create.
    unfold CompactLogs.log_empty.
    rewrite getenv_create.
    reflexivity.
  Defined.

  Disable Notation "'let/opt' v1 ':=' expr 'in' body".
  Disable Notation "'let/opt2' v1 ',' v2 ':=' expr 'in' body".


  Lemma opt_bind_none {A B} {f : A -> option B} :
    forall x : option A,
    x = None ->
    opt_bind x f = None.
  Proof. intros x H. rewrite H. reflexivity. Defined.

  Lemma compact_typed_eq_abort {env : REnv.(env_t) R} :

    (CompactSemantics.interp_action env sigma_denote Gamma CompactLogs.log_empty CompactLogs.log_empty a) = None
    <->
    (TypedSemantics.interp_action env sigma_denote Gamma Logs.log_empty Logs.log_empty a) = None.
  Proof.
    induction a.
    - simpl; split; (reflexivity + discriminate).
    - simpl; split; (reflexivity + discriminate).
    - simpl; split; (reflexivity + discriminate).
    - simpl.
      repeat match goal with
      | |- context [let '(_,_) := ?x in _] => destruct x
      | |- context [opt_bind ?x] => destruct x eqn:?H; simpl
      end.
      + split; (reflexivity + discriminate).
      + split; try (reflexivity + discriminate).
        specialize (IHa0 Gamma a0). rewrite H in IHa0. rewrite H0 in IHa0. destruct IHa0. specialize (H2 eq_refl). discriminate.
      + split; try (reflexivity + discriminate).
        specialize (IHa0 Gamma a0). rewrite H in IHa0. rewrite H0 in IHa0. destruct IHa0. specialize (H1 eq_refl). discriminate.
      + split; (reflexivity + discriminate).
    - simpl.
      repeat match goal with
      | |- context [let '(_,_) := ?x in _] => destruct x
      | |- context [opt_bind ?x] => destruct x eqn:?H; simpl
      end.
      unfold opt_bind.
      repeat match goal with
      |- context [match ?x with | _ => _ end] => destruct x eqn:?
      end.
      all: split.
      all: try discriminate; try reflexivity.
      specialize (IHa0 Gamma a0).
      destruct IHa0.
      set (H0 Heqo0).
      rewrite e in Heqo.
      discriminate.
      admit.
    -

      match goal with
      |- context [match ?x with | Some _ => _ | None => _ end] => destruct x eqn:l
      end.
      + split. destruct p. destruct p.  discriminate.
        destruct p0. destruct p0. discriminate.
      +
      specialize (IHa0 Gamma a0).
       rewrite p in IHa0.
      match goal with
      |- context [match ?x with | _ => _ end] => destruct x
      end.
    rewrite ?opt_bind_none.  unfold opt_bind.
    
    split; discriminate.
    - simpl.
    split.



  Lemma compact_typed_eq :
    let env := REnv.(create) r in

    option_map
      (fun '(log,out,_) => (CompactLogs.commit_update env log, out))
      (CompactSemantics.interp_action env sigma_denote Gamma CompactLogs.log_empty CompactLogs.log_empty a)
    =
    option_map
      (fun '(log,out,_) => (Logs.commit_update env log, out))
      (TypedSemantics.interp_action env sigma_denote Gamma Logs.log_empty Logs.log_empty a).
  Proof.
    intros.
    induction a.
    - unfold CompactSemantics.interp_action, TypedSemantics.interp_action, option_map. reflexivity.
    - unfold CompactSemantics.interp_action, TypedSemantics.interp_action, option_map.
        try rewrite CompactLogs_commit_update_empty;
        try rewrite Logs_commit_update_empty;
        reflexivity.
    - unfold CompactSemantics.interp_action, TypedSemantics.interp_action, option_map.
      try rewrite CompactLogs_commit_update_empty;
      try rewrite Logs_commit_update_empty;
      reflexivity.
    - simpl.
      Locate opt_bind.
      unfold opt_bind.
      unfold option_map.
      unfold option_map in IHa0.
      match goal with
      |- context [match ?y with | Some x => (let '(p, Gamma0) := x in
                                            let '(action_log, v) := p in
                                            Some (action_log, Ob, creplace m v Gamma0))
                                | None => None end] =>
        fold (option_map (fun x => let '(p, Gamma0) := x in
                                   let '(action_log, v) := p in
                                   Some (action_log, Ob, creplace m v Gamma0)) y)
      end.

  Search (option).

      unfold

      apply IHa0.
      assumption.
      unfold option_map.
      CompactSemantics.interp_action, TypedSemantics.interp_action, option_map.
      try rewrite CompactLogs_commit_update_empty;
      try rewrite Logs_commit_update_empty;
      reflexivity.
End CompactEquality.
