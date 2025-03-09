(* Implementing hoare logic for koika's evaluation *)
Require Import Unicode.Utf8.

Require Import Koika.TypedSyntax.
Require Import Koika.TypedSemantics.

Require Import Koika.SemanticProperties.
Require Import IdentParsing.
(* for more details about hoare triples refer to the
 * software foundations book:
 * https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
 *)

Lemma latest_write_cons_read : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) r1 r2 p,
  latest_write (log_cons r1 {| kind := LogRead; port := p; val := tt |} l) r2 = latest_write l r2.
Proof.
  intros; unfold latest_write, log_find, log_cons.
  destruct (eq_dec r1 r2) as [Heq|Hneq].
  + now rewrite Heq, get_put_eq.
  + now rewrite get_put_neq.
Qed.

Lemma commit_read : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) reg port env,
  commit_update env (log_cons reg {| kind := LogRead; port := port; val := tt |} l) = commit_update env l.
Proof.
  intros; unfold commit_update.
  apply create_funext; intro.
  now rewrite latest_write_cons_read.
Qed.

Lemma commit_write : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) reg port val env,
  commit_update env (log_cons reg {| kind := LogWrite; port := port; val := val |} l) = (REnv.(putenv) (commit_update env l) reg val).
Proof.
  intros; unfold commit_update.
  apply equiv_eq; unfold equiv; intros.
  rewrite getenv_create.
  destruct (eq_dec k reg).
  - subst. now rewrite get_put_eq, latest_write_cons_eq.
  - now rewrite get_put_neq, getenv_create, latest_write_cons_neq by easy.
Qed.

Lemma commit_read_log : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) env,
  (∀ reg, log_existsb l reg is_write0 = false) ->
  (∀ reg, log_existsb l reg is_write1 = false) ->
  commit_update env l = env.
Proof.
  intros; unfold commit_update.
  apply equiv_eq; intro.
  rewrite getenv_create.
  now rewrite latest_write_None.
Qed.

Lemma commit_read_log_get : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) env reg,
  log_existsb l reg is_write0 = false ->
  log_existsb l reg is_write1 = false ->
  getenv REnv (commit_update env l) reg = getenv REnv env reg.
Proof.
  intros; unfold commit_update.
  rewrite getenv_create.
  now rewrite latest_write_None.
Qed.

Lemma list_find_opt_app_some : ∀ A B l l' x (fn: A -> option B),
  list_find_opt fn l = Some x -> list_find_opt fn (l ++ l') = Some x.
Proof.
  intros.
  induction l. inversion H.
  cbn in H.
  destruct (fn a) eqn:Ha.
  cbn. now rewrite Ha, H.
  cbn. rewrite Ha.
  auto.
Qed.

Lemma list_find_opt_app_none : ∀ A B l l' (fn: A -> option B),
  list_find_opt fn l = None -> list_find_opt fn (l ++ l') = list_find_opt fn l'.
Proof.
  intros.
  induction l. reflexivity.
  cbn in H.
  destruct (fn a) eqn:Ha.
  inversion H.
  cbn. rewrite Ha.
  auto.
Qed.

Lemma commit_update_app : ∀ reg_t(*  `{FiniteType reg_t}  *){R : reg_t -> type} {REnv : Env reg_t} (l1 l2 : Log R REnv) env,
  commit_update (commit_update env l2) l1 = commit_update env (log_app l1 l2).
Proof.
  intros.
  unfold commit_update.
  apply create_funext.
  intro.
  rewrite getenv_create.
  destruct (latest_write l1 k) eqn:Hl2.
  unfold log_app, map2.
  unfold latest_write, log_find.
  rewrite getenv_create.
  erewrite list_find_opt_app_some. reflexivity. assumption.
  unfold latest_write, log_find, log_app, map2. rewrite getenv_create. now rewrite list_find_opt_app_none.
Qed.

Lemma log_app_inv_tail : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l l1 l2: Log R REnv),
 log_app l1 l = log_app l2 l ->
 l1 = l2.
Proof.
  intros reg_t R REnv * H.
  apply equiv_eq in H.
  unfold log_app, equiv in H.
  setoid_rewrite getenv_map2 in H.
  setoid_rewrite app_inv_tail_iff in H.
  apply equiv_eq in H.
  assumption.
Qed.

Lemma may_read_empty : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} p r,
  @may_read _ R REnv log_empty log_empty p r = true.
Proof.
  intros.
  unfold may_read.
  destruct p; [apply andb_true_iff; split|];
  now rewrite log_existsb_app, negb_true_iff, log_existsb_empty.
Qed.

Lemma log_cons_app : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} r le (l1 l2: Log R REnv),
  log_cons r le (log_app l1 l2) = log_app (log_cons r le l1) l2.
Proof.
  intros.
  apply equiv_eq; unfold equiv, log_cons, log_app, map2.
  intros.
  destruct (eq_dec k r) as [Heq | Heq].
  - rewrite Heq, ?getenv_create, ?get_put_eq.
    apply app_comm_cons.
  - now rewrite get_put_neq, ?getenv_create, get_put_neq.
Qed.

Ltac simpl_hoare :=
  repeat match goal with
  | H: interp_action _ _ _ _ _ ?a = Some _ |- _ => head_constructor a; cbn in H
  | H: interp_args _ _ _ _ _ ?a = Some _ |- _ => head_constructor a; cbn in H
  | H: opt_bind ?a _ = Some _ |- _ => destruct a eqn:?Heq; inversion H; clear H
  | H: prod _ _ |- _ => destruct H
  | H: and _ _ |- _ => destruct H
  | H: Some _ = Some _ |- _ => apply Some_inj in H
  | H: pair _ _ = pair _ _ |- _ => apply pair_inj in H
  | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?
  (* | H: (if ?x then _ else _) = Some _ |- _ => destruct x eqn:? *)
  | H: ?A = ?A |- _ => clear H
  | H: ?B = true |- context[?B] => rewrite H
  | H: ?B = false |- context[?B] => rewrite H
  | H: context[may_read] |- _ => unfold may_read in H
  | H: context[may_write] |- _ => unfold may_write in H
  | |- context[may_read] => unfold may_read
  | |- context[may_write] => unfold may_write
  | H: context[latest_write0 (log_app _ _ )] |- _ => rewrite latest_write0_app in H
  | H: latest_write0 ?l ?r = Some _ |- context[latest_write0 ?l ?r] => rewrite H
  | H: latest_write0 ?l ?r = None   |- context[latest_write0 ?l ?r] => rewrite H
  | H: _ && _ = true |- _ => apply andb_prop in H
  | H: _ || _ = false |- _ => rewrite orb_false_iff in H
  | H: negb _ = true |- _ => rewrite negb_true_iff in H
  | H: context[log_existsb (log_app _ _)] |- _ => rewrite log_existsb_app in H
  | |- context[log_existsb (log_app _ _)] => rewrite log_existsb_app
  | |- context[latest_write0 (log_app _ _)] => rewrite latest_write0_app
  | H1: log_existsb ?l ?reg is_write0 = false,
    H2: log_existsb ?l ?reg is_write1 = false |-
      context[latest_write ?l ?reg] => rewrite latest_write_None by assumption
  | |- context[getenv _ (commit_update _ _) _] => rewrite getenv_commit_update
  | H: log_existsb ?l ?idx is_write1 = false |- context[latest_write ?l ?idx] =>
    rewrite latest_write_latest_write0 by assumption
  | |- context[opt_bind (Some _) _] => cbn
  | |- context[opt_bind None _] => cbn
  | _ => progress subst
  | _ => progress cbn
  | _ => easy
  end.

Section Hoare.

  Context {var_t : Type}.
  Context {reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.

  #[local] Notation action := (TypedSyntax.action unit var_t string R Sigma).
  #[local] Notation acontext := (@TypedSemantics.acontext unit var_t string _ _ R Sigma).

  #[local] Ltac simpl_hoare' custom :=
    repeat (simpl_hoare + custom).

  #[local] Tactic Notation "simpl_hoare" "[" tactic(c) "]" :=
    (simpl_hoare' c).

  #[local] Ltac clear_all keep :=
    repeat match goal with
      | H: _ |- _ => lazymatch H with
        | keep => fail
        | _ => clear H
        end
      end.

  #[local] Tactic Notation "clear_all" "keep[" hyp(k) "]" :=
    clear_all k.

  Local Ltac solve_shed_log_irr := simpl_hoare [try match goal with
    | H: ∀ _ _ _ _ _ _ _ _ _,
      interp_action _ _ _ (log_app _ _) _ _ = Some _ ->
      interp_action _ _ _ _ _ _ = Some _,
      H1: interp_action _ _ _ (log_app ?sl ?sl2 ) ?al ?a = Some _ |-
      context[interp_action (commit_update _ ?sl2) _ _ ?sl ?al ?a] =>
      setoid_rewrite (H _ _ _ _ _ _ _ _ _ H1)
    | H: ∀ _ _ _ _ _ _ _ _ _,
      interp_args _ _ _ (log_app _ _) _ _ = Some _ ->
      interp_args _ _ _ _ _ _ = Some _,
      H1: interp_args _ _ _ (log_app ?sl ?sl2 ) ?al ?a = Some _ |-
      context[interp_args (commit_update _ ?sl2) _ _ ?sl ?al ?a] =>
      setoid_rewrite (H _ _ _ _ _ _ _ _ _ H1)
    end].
  (* We can actually only proof an implication here since some evaluations might
    fail with a None on the longer scheduler log, but succeed with a Some on the
    shortened version *)
  Lemma interp_slog_irrelevance :
    ( ∀ {sig tau} {a : action sig tau},
      ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog slog' alog alog_out r},
      interp_action env sigma Γ (log_app slog slog') alog a = Some (alog_out, r, Γ') ->
      interp_action (commit_update env slog') sigma Γ slog alog a = Some (alog_out, r, Γ') )
    /\
    ( ∀ {sig argspec} {args : acontext sig argspec},
      ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog slog' alog alog_out r},
      interp_args env sigma Γ (log_app slog slog') alog args = Some (alog_out, r, Γ') ->
      interp_args (commit_update env slog') sigma Γ slog alog args = Some (alog_out, r, Γ') ).
  Proof.
    apply action_ind_complete; intros; solve_shed_log_irr.
  Qed.

  Lemma interp_action_slog_irrelevance :
    ∀ {sig tau} {a : action sig tau},
    ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog slog' alog alog_out r},
    interp_action env sigma Γ (log_app slog slog') alog a = Some (alog_out, r, Γ') ->
    interp_action (commit_update env slog') sigma Γ slog alog a = Some (alog_out, r, Γ').
    apply interp_slog_irrelevance. Qed.

  Lemma interp_args_slog_irrelevance :
    ∀ {sig argspec} {args : acontext sig argspec},
    ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog slog' alog alog_out r},
    interp_args env sigma Γ (log_app slog slog') alog args = Some (alog_out, r, Γ') ->
    interp_args (commit_update env slog') sigma Γ slog alog args = Some (alog_out, r, Γ').
    apply interp_slog_irrelevance. Qed.

  Local Ltac solve_act_log_irr := simpl_hoare [try match goal with
  | H: ∀ _ _ _ _ _ _ _ _ _,
    interp_action _ _ _ _ (log_app _ _) _ = Some _ ->
    ∃ _, _,
    H1: interp_action _ _ _ ?sl (log_app ?al1 ?al2) ?a = Some _ |-
    context[interp_action _ _ _ (log_app ?al2 ?sl) ?al1 ?a] =>
    let H' := fresh "H" in
    pose proof (H' := H _ _ _ _ _ _ _ _ _ H1);
    destruct H' as [?l [H' ?]]; subst;
    setoid_rewrite H'
  | H: ∀ _ _ _ _ _ _ _ _ _,
    interp_args _ _ _ _ (log_app _ _) _ = Some _ ->
    ∃ _, _,
    H1: interp_args _ _ _ ?sl (log_app ?al1 ?al2) ?a = Some _ |-
    context[interp_args _ _ _ (log_app ?al2 ?sl) ?al1 ?a] =>
    let H' := fresh "H" in
    pose proof (H' := H _ _ _ _ _ _ _ _ _ H1);
    destruct H' as [?l [H' ?]]; subst;
    setoid_rewrite H'
  | |- context[log_cons _ _ (log_app _ _)] => rewrite log_cons_app by easy
  | _ => solve [eexists; split; reflexivity]
  end].

  Context `{FiniteType reg_t}.

  Lemma interp_alog_irrelevance :
    ( ∀ {sig tau} {a : action sig tau},
      ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog alog alog' alog_out r},
      interp_action env sigma Γ slog (log_app alog' alog) a = Some (alog_out, r, Γ') ->
      exists alog_out',
      interp_action env sigma Γ (log_app alog slog) alog' a = Some (alog_out', r, Γ') /\
      alog_out = log_app alog_out' alog )
    /\
    ( ∀ {sig argspec} {args : acontext sig argspec},
      ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog alog alog' alog_out r},
      interp_args env sigma Γ slog (log_app alog' alog) args = Some (alog_out, r, Γ') ->
      exists alog_out',
      interp_args env sigma Γ (log_app alog slog) alog' args = Some (alog_out', r, Γ') /\
      alog_out = log_app alog_out' alog ).
  Proof.
    apply action_ind_complete; intros; solve_act_log_irr.
  Qed.

  Lemma interp_action_alog_irrelevance :
    ∀ {sig tau} {a : action sig tau},
    ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog alog alog' alog_out r},
    interp_action env sigma Γ slog (log_app alog' alog) a = Some (alog_out, r, Γ') ->
    exists alog_out',
    interp_action env sigma Γ (log_app alog slog) alog' a = Some (alog_out', r, Γ') /\
    alog_out = log_app alog_out' alog. apply (interp_alog_irrelevance). Qed.

  Lemma interp_args_alog_irrelevance :
    ∀ {sig argspec} {args : acontext sig argspec},
    ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog alog alog' alog_out r},
    interp_args env sigma Γ slog (log_app alog' alog) args = Some (alog_out, r, Γ') ->
    exists alog_out',
    interp_args env sigma Γ (log_app alog slog) alog' args = Some (alog_out', r, Γ') /\
    alog_out = log_app alog_out' alog. apply (interp_alog_irrelevance). Qed.

  Theorem interp_action_log_irrelevance :
    ∀ {sig tau} {a : action sig tau},
    ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog alog alog_out r},
    interp_action env sigma Γ slog alog a = Some (alog_out, r, Γ') ->
    exists alog_out',
    interp_action (commit_update env (log_app alog slog)) sigma Γ log_empty log_empty a = Some (alog_out', r, Γ') /\
    alog_out = log_app alog_out' alog.
  Proof.
    intros * H'.
    rewrite <- (log_app_empty_r alog) in H'.
    pose proof (Ha := interp_action_alog_irrelevance H').
    destruct Ha as [log [Ha Hlog]].
    rewrite <- (log_app_empty_r (log_app _ _)) in Ha.
    pose proof (Hs := interp_action_slog_irrelevance Ha).
    eexists log.
    now split.
  Qed.

  Theorem interp_args_log_irrelevance :
    ∀ {sig argspec} {args : acontext sig argspec},
    ∀ {env : REnv.(env_t) R} {sigma Γ Γ' slog alog alog_out r},
    interp_args env sigma Γ slog alog args = Some (alog_out, r, Γ') ->
    exists alog_out',
    interp_args (commit_update env (log_app alog slog)) sigma Γ log_empty log_empty args = Some (alog_out', r, Γ') /\
    alog_out = log_app alog_out' alog.
  Proof.
    intros * H'.
    rewrite <- (log_app_empty_r alog) in H'.
    pose proof (Ha := interp_args_alog_irrelevance H').
    destruct Ha as [log [Ha Hlog]].
    rewrite <- (log_app_empty_r (log_app _ _)) in Ha.
    pose proof (Hs := interp_args_slog_irrelevance Ha).
    eexists log.
    now split.
  Qed.

  Context {sig: tsig var_t}.
  Section HoareTriple.
    Context {tau: type}.

    (** An _assertion_ is a logical claim about the state of a circuit

      This state consists of the register environment, the variable valuation (Gamma/Γ),
      the scheduler log and the current action log.

      Unfortunately, the scheduler/action log and the register environment cannot be
      combined into a single 'register state'. One might think it should be possible,
      since problems like multiple writes to the same register are already eliminated
      by assuming (in `hoare_triple`) that `interp_action` evaluated to `Some _`. However,
      consider the case where a read0 is used after a write0 (which is considered bad style but
      legal koika). In this case the read0 should observe the value from the beginning of
      the cycle. However when merging the logs and the environment into a single state - we
      would no longer know if the register value in this state is still the one from the
      beginning of the cycle or the one from a previous `write1`.

      Letz go over that again with a specific example. Assume we would have merge the
      logs and the env. Now we would like to proove this property.

      {{ env.[reg] = 5 }} <{ read0(reg) }> {{ ret = 5 }}

      However, we would fail, as coq would bring to our attention that `reg = 5` might also
      be the result of `env.[reg] = 3` and `action_log = [write0(reg, 5)]`.

      So its turns out, we actually cannot prove our postcondition in every possible state that
      satisfies our precondition.
      *)
    (* an assertion depends on the current register state `env`
      and then local variable context `Gamma` or `Γ` *)
    Definition assertion := REnv.(env_t) R -> tcontext sig -> Prop.
    (* the return assertion additionally gets the returned value
      of an action to reason about *)
    Definition ret_assertion := tau -> assertion.
    Definition ret_assertion' {argspec : tsig var_t} := tcontext argspec ->  assertion.

    (* an assertion expression *)
    Definition a_exp {t : type} := REnv.(env_t) R -> tcontext sig -> t.
    Definition ret_a_exp {t : type} := tau -> @a_exp t.

    (* This definition implements the idea of hoare logic for
      koika. (refer to https://en.wikipedia.org/wiki/Hoare_logic)

      Here we define hoare triples based on the evaluation of `interp_action`
      using empty logs as the scheduler and action log. At first, this might
      seem like a weaker proposition than all-quantifying these logs, however
      please note how it enables us to reason over the current register state
      in a much more concise manner.

      Consider the following example, where we all-quantify the logs and then
      try to express the precondition that the register `reg1` has the value 5.

      In this case it wouldn't suffice to state that

      `{{ env.[reg1] = 5 }} ... {{ .. }}`

      because we could easily come up with a pair of logs that write to `reg1`
      and effectively change its current state. Consequently, in order to even
      state our desired precondition, the assertions would additionally need
      reason over both log. Suppose they could, then we would probably state
      something similar to this:

      `{{ (env.[reg1] = 5 /\ latest_write slog reg1 = None /\ latest_write alog reg1 = None) \/
          (exists a, latest_write slog reg1 = Some a /\ a = 5 /\ latest_write alog reg1 = None ) \/
          (exists a, latest_write alog reg1 = Some a /\ a = 5)
      }} ... {{ .. }}`

      With this proposition we would have coveres all cases, either `reg1` was
      written in the action log and the written value is 5 or it was only
      written in the scheduler log, or it wasn't written at all and its prior
      value was 5.

      And while it might be possible to hide this monstrosity of a precondition
      with some fancy notations, reasoning with multiple logs turns out quite painful.

      As a consequence, I decided to state this theorem with empty logs, such that the
      assertions only need to reason over the current environment state. And to make
      hoare triples more meaningful, I've prooven a seperate theorem, which shows that
      all properties that hold on empty logs also apply to all-quantified logs.
      However, while this seems to goog to be true, there is a small catch, I had to
      add a restriction to the `read0` command. This restriction forbids using a `read0`
      on a registers that was written before. Prior to this work, the `read0` would
      simply always return the value from the start of the cycle. Nevertheless, using
      `read0` this way was already considered bad style and even forbidding it does
      not reduce the expressiveness of Koika. The same effect can be accomplished
      by invoking `read0` prior to any writes and saving the value in a local variable.
       *)
    (* Note: the order of the arguments is choosen to enable better typechecking -
     *   typically the type of the action is known precisely and we want to infer
     *   the types of the pre-condition and post-condition from it. Thus the
     *   action is passed first and then P and Q. This detail is going to be hidden
     *   in the notation anyway.
     *)
    Context {sigma : (∀ f : ext_fn_t, Sig_denote (Sigma f))}.
    Definition hoare_triple
      (a : action sig tau) (P : assertion) (Q : ret_assertion) : Prop :=
      ∀ env Γ Γ' log r,
      P env Γ ->
      interp_action env sigma Γ log_empty log_empty a = Some (log, r, Γ') ->
      Q r (commit_update env log) Γ'.

    Definition hoare_triple_args {argspec}
      (args : acontext sig argspec) (P : assertion) (Q : ret_assertion') : Prop :=
      ∀ env Γ Γ' log r_ctx,
      P env Γ ->
      interp_args env sigma Γ log_empty log_empty args = Some (log, r_ctx, Γ') ->
      Q r_ctx (commit_update env log) Γ'.

    (* This lemma prooves the log irrelevance -
     *
     * if an assertion holds on empty logs then it holds on every pair of logs
     *)
    Lemma hoare_log_irr : ∀ P a Q,
      hoare_triple a P Q ->
      ∀ env Γ Γ' slog alog alog' r,
      P (commit_update env (log_app alog slog)) Γ ->
      interp_action env sigma Γ slog alog a = Some (alog', r, Γ') ->
      Q r (commit_update env (log_app alog' slog)) Γ'.
    Proof.
      intros * Hht env Γ Γ' slog alog alog' r HP Hin.
      unfold hoare_triple in Hht.
      apply interp_action_log_irrelevance in Hin.
      destruct Hin as [? [Hin  Hlog]].
      specialize (Hht _ _ _ _ _ HP Hin).
      now rewrite commit_update_assoc, log_app_assoc, <- Hlog in Hht.
    Qed.

    Lemma hoare_log_irr_args {argspec: tsig var_t} : ∀ P (args : acontext sig argspec) Q,
      hoare_triple_args args P Q ->
      ∀ env Γ Γ' slog alog alog' r,
      P (commit_update env (log_app alog slog)) Γ ->
      interp_args env sigma Γ slog alog args = Some (alog', r, Γ') ->
      Q r (commit_update env (log_app alog' slog)) Γ'.
    Proof.
      intros * Hht * HP Hin.
      unfold hoare_triple_args in Hht.
      apply interp_args_log_irrelevance in Hin.
      destruct Hin as [? [Hin  Hlog]].
      specialize (Hht _ _ _ _ _ HP Hin).
      now rewrite commit_update_assoc, log_app_assoc, <- Hlog in Hht.
    Qed.

  End HoareTriple.
End Hoare.

Section HoareCoercions.
  Context {var_t reg_t : Type} {R: reg_t -> type} {sig: tsig var_t} {REnv: Env reg_t}.
  Context {tau : type}.

  Notation assertion := (@assertion var_t reg_t R REnv sig).
  Notation ret_assertion := (@ret_assertion var_t reg_t R REnv sig).
  Notation a_exp := (@a_exp var_t reg_t R REnv sig).
  Notation ret_a_exp := (@ret_a_exp var_t reg_t R REnv sig).

  Coercion assertion_of_Prop (P : Prop) : assertion := fun _ _ => P.
  #[warnings="-uniform-inheritance"]
  Coercion ret_assertion_of_assertion (a : assertion) : @ret_assertion tau := fun _ => a.
  (* Coercion ret_assertion_of_Prop (P : Prop) : @ret_assertion tau := fun _ _ _ => P. *)


  Coercion a_exp_of_type {t : type} (v : t) : a_exp := fun _ _ => v.
  (* Definition a_exp_of_anything {type : Type} {t : type} {denote : type -> Type} (v : (denote t)) : @a_exp type t denote := fun _ _ => v. *)
  (* Coercion a_exp_of_reg (r : reg_t) : a_exp := fun env _ => env?[r]. *)
  (* Coercion a_exp_of_var (s : string) : a_exp := fun _ Γ => Γ.[r]. *)

  (* #[warnings="-uniform-inheritance"]
  Coercion ret_a_exp_of_exp {tau} {t : type} (a : a_exp) : @ret_a_exp tau t := fun _ => a. *)



End HoareCoercions.

(* Coercion type_to_nat {τ : type} (v : τ) := Bits.to_nat (bits_of_value v). *)
#[warnings="-uniform-inheritance"]
Coercion nat_to_type {τ : type} (n : nat) := @value_of_bits τ (Bits.of_nat _ n).

#[warnings="-uniform-inheritance", reversible=no]
Coercion action_of_function {pos_t var_t} {fn_name_t} {reg_t ext_fn_t} {sig tau}
    {R : reg_t -> type} {Sigma: ext_fn_t -> ExternalSignature} :=
    @int_body fn_name_t (TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau).

Print action_of_function.

Definition test1 := (5 : bits_t 4).
Definition test2 {var_t reg_t R REnv sig tau} := (5 : @a_exp var_t reg_t R REnv sig tau).

(* This typeclass is necessary to make sure the variable identifier is
 * known when the typeclass resolution starts.
 *
 * Assume trying this instead:
 *   Existing Class member
 *   Existing Instance MemberHd
 *   Existing Instance MemberTl
 *
 * In this case resolution would try to find `member (?__i, ?t) sig` and
 * trivially apply the first contructor found (typically MemberHd).
 * However, if the typeclass resolution used for the ident-parsing would
 * now try to resolve ?__i to "b" which might be only the 2nd entry in sig
 * it would fail. (After all we would want ident-parsing to run first)
 *
 * To achieve this order, we have to use something like `Hint Mode member + + +`
 * and thereby force the resolution for member to wait until the arguments are
 * completely resolved.
 *
 * Unfortunately also this does not work, because even after ident-parsing only
 * ?__i is resolved and ?t is still unknown (we would like to resolve ?t by finding
 * a member proof, but we cannot express that using `Hint Mode` - in other words:
 * it is not possible that part of an argument is considered 'input' and another
 * part 'output')
 *
 * Therefore, VarCtxMember splits these two arguments into seperate inputs and
 * specifies their mode accordingly
 *)
Class VarCtxMember {var_t} {t : type} (k : var_t) sig :=
  var_ctx_member : member (k,t) sig.
Arguments var_ctx_member {var_t} {t} k sig {VarCtxMember}.
Instance VarCtxMemberHd {var_t} {t : type} (k : var_t) sig : @VarCtxMember _ t k ((k,t) :: sig) :=
  MemberHd (k,t) sig.
Instance VarCtxMemberTl {var_t} {t t' : type} {k'} k sig (m : @VarCtxMember _ t k sig) : @VarCtxMember var_t t k ((k',t') :: sig) :=
  MemberTl (k,t) (k',t') sig (@var_ctx_member _ _ _ _ m).
Hint Mode VarCtxMember - - + +  : typeclass_instances.

Module Export HoareNotations.
  Declare Custom Entry assertion.

  (* Declare Scope assertion_scope.
  Bind Scope assertion_scope with assertion.
  Delimit Scope assertion_scope with assertion. *)

  (* We need both here - the scope delimiter to make sure our notations can be nested
    and the type annotations to let the coercions kick in  *)
  Notation "P -> Q"  := (fun env Γ =>  (P : assertion) env Γ ->  (Q : assertion) env Γ) (in custom assertion at level 99).
  Notation "P <-> Q" := (fun env Γ =>  (P : assertion) env Γ <-> (Q : assertion) env Γ) (in custom assertion at level 95).
  Notation "P /\ Q"  := (fun env Γ =>  (P : assertion) env Γ /\  (Q : assertion) env Γ) (in custom assertion at level 80).
  Notation "P \/ Q"  := (fun env Γ =>  (P : assertion) env Γ \/  (Q : assertion) env Γ) (in custom assertion at level 85).
  Notation "~ P"     := (fun env Γ => ~(P : assertion) env Γ) (in custom assertion at level 75).

  (* Declare Scope assertion_expr_scope.
  Bind Scope assertion_expr_scope with a_exp.
  Delimit Scope assertion_expr_scope with a_exp. *)

  Notation "a = b"  := (fun env Γ => (a : a_exp) env Γ =  (b : a_exp) env Γ) (in custom assertion at level 70).
  Notation "a <> b" := (fun env Γ => (a : a_exp) env Γ <> (b : a_exp) env Γ) (in custom assertion at level 70).
  Notation "a <= b" := (fun env Γ => (a : a_exp) env Γ <= (b : a_exp) env Γ) (in custom assertion at level 70).
  Notation "a < b"  := (fun env Γ => (a : a_exp) env Γ <  (b : a_exp) env Γ) (in custom assertion at level 70).
  Notation "a >= b" := (fun env Γ => (a : a_exp) env Γ >= (b : a_exp) env Γ) (in custom assertion at level 70).
  Notation "a > b"  := (fun env Γ => (a : a_exp) env Γ >  (b : a_exp) env Γ) (in custom assertion at level 70).

  Notation "f x .. y" := (fun env Γ => let f' := (f env Γ) in (.. (f' (x env Γ)) .. (y env Γ)))
    (in custom assertion at level 1, x custom assertion at level 0, y custom assertion at level 0, f custom assertion).
  Notation "a" := (fun env Γ => a) (in custom assertion at level 0, a constr at level 0).

  Notation "'env'" := (fun env Γ => env) (in custom assertion).
  Notation "'env' '[' reg ']'"     := (fun env Γ => (getenv _ env reg) ) (in custom assertion, reg constr, format "env [ reg ]").

  Notation "'Γ'" := (fun env Γ => Γ) (in custom assertion).
  Notation "'Γ' '[' f ']'" := (fun env => cassoc (var_ctx_member (IdentParsing.ident_to_string f : string) _)) (in custom assertion, f constr at level 0, only parsing).
  Notation "'Γ' '[' f ']'" := (fun _ => @cassoc _ _ _ (f : string,_) _) (in custom assertion, f constr at level 0, only printing).

  Notation "'(' a ')'" := (a) (in custom assertion).
  Notation "'`' a '`'" := (a) (in custom assertion, a constr at level 0).
  Notation "'$' a" := (a) (in custom assertion at level 0, a constr at level 0, format "$ a").

  Module TestNotations.
  Section TestNotations.
    Context {reg_t} {R: reg_t -> type} {REnv: Env reg_t}.
    Definition sig: tsig string := [("a", bits_t 1); ("b", bits_t 5)].
    Notation assertion := (@assertion string reg_t R REnv sig).
    Notation a_exp := (@a_exp string reg_t R REnv sig).
    Context (P Q : assertion).
    Context (reg0 : reg_t).

    Notation "'{{' P '}}'" := (P) (at level 10, P custom assertion).

    Definition test1 : assertion := {{ `P` }}.
    Definition test2 : assertion := {{ True }}.
    Definition test3 : a_exp     := {{ env[reg0] }}.
    (* Definition idk : a_exp := (fun env => get_ctx_element (var_ctx_member (IdentParsing.ident_to_string b : string) _)). *)
    Definition test4 : a_exp     := {{ Γ[b] }}.
    Definition test5 : assertion := {{ Γ[b] = 5 }}.
    Definition test6 : assertion := {{ `P` /\ `Q` }}.
    Definition test7 : assertion := {{ `P` /\ (`Q` \/ $P) }}.
    Definition test8 : assertion := {{ `P` /\ (`Q` \/ ~`P`) \/ Γ[b] = Γ[b]}}.
    Definition test9 : assertion := {{ `fun env Γ => P env Γ` /\ `Q` }}.
    Definition test10 : assertion := {{ P env Γ /\ $Q }}.

  End TestNotations.
  End TestNotations.

  Declare Custom Entry ret_assertion.

  (* Declare Scope ret_assertion_scope.
  Bind Scope ret_assertion_scope with ret_assertion.
  Delimit Scope ret_assertion_scope with ret_assertion. *)

  Notation "r ',' P" := (fun r => (P : assertion)) (in custom ret_assertion at level 0, P custom assertion at level 200, r constr at level 0 as name).

  Notation "P -> Q"  := (fun ret env Γ =>  (P : ret_assertion) ret env Γ ->  (Q : ret_assertion) ret env Γ) (in custom ret_assertion at level 99).
  Notation "P <-> Q" := (fun ret env Γ =>  (P : ret_assertion) ret env Γ <-> (Q : ret_assertion) ret env Γ) (in custom ret_assertion at level 95).
  Notation "P /\ Q"  := (fun ret env Γ =>  (P : ret_assertion) ret env Γ /\  (Q : ret_assertion) ret env Γ) (in custom ret_assertion at level 80).
  Notation "P \/ Q"  := (fun ret env Γ =>  (P : ret_assertion) ret env Γ \/  (Q : ret_assertion) ret env Γ) (in custom ret_assertion at level 85).
  Notation "~ P"     := (fun ret env Γ => ~(P : ret_assertion) ret env Γ) (in custom ret_assertion at level 75).

  (* Declare Scope ret_assertion_expr_scope.
  Bind Scope ret_assertion_expr_scope with ret_a_exp.
  Delimit Scope ret_assertion_expr_scope with ret_a_exp. *)

  Notation "a = b"  := (fun ret env Γ => (a : ret_a_exp) ret env Γ =  (b : ret_a_exp) ret env Γ) (in custom ret_assertion at level 70).
  Notation "a <> b" := (fun ret env Γ => (a : ret_a_exp) ret env Γ <> (b : ret_a_exp) ret env Γ) (in custom ret_assertion at level 70).
  Notation "a <= b" := (fun ret env Γ => (a : ret_a_exp) ret env Γ <= (b : ret_a_exp) ret env Γ) (in custom ret_assertion at level 70).
  Notation "a < b"  := (fun ret env Γ => (a : ret_a_exp) ret env Γ <  (b : ret_a_exp) ret env Γ) (in custom ret_assertion at level 70).
  Notation "a >= b" := (fun ret env Γ => (a : ret_a_exp) ret env Γ >= (b : ret_a_exp) ret env Γ) (in custom ret_assertion at level 70).
  Notation "a > b"  := (fun ret env Γ => (a : ret_a_exp) ret env Γ >  (b : ret_a_exp) ret env Γ) (in custom ret_assertion at level 70).

  Notation "f x .. y" := (fun ret env Γ => let f' := (f ret env Γ) in (.. (f' (x ret env Γ)) .. (y ret env Γ)))
    (in custom ret_assertion at level 0, x custom ret_assertion at level 0, y custom ret_assertion at level 0, f custom ret_assertion).
  Notation "a" := (fun ret env Γ => a) (in custom ret_assertion at level 0, a constr at level 0).


  Notation "'env'" := (fun ret env Γ => env) (in custom ret_assertion).
  Notation "'env' '[' reg ']'"     := (fun ret env Γ =>              (getenv _ env reg) ) (in custom ret_assertion, reg constr, format "env [ reg ]").

  Notation "'Γ'" := (fun ret env Γ => Γ) (in custom ret_assertion).
  Notation "'Γ' '[' f ']'" := (fun ret env => cassoc (var_ctx_member (IdentParsing.ident_to_string f : string) _)) (in custom ret_assertion, f constr at level 0, only parsing).
  Notation "'Γ' '[' f ']'" := (fun _ _ => @cassoc _ _ _ (f : string,_) _) (in custom ret_assertion, f constr at level 0, only printing).

  Notation "'(' a ')'" := (a) (in custom ret_assertion).
  Notation "'`' a '`'" := (a) (in custom ret_assertion, a constr).
  Notation "'$' a" := (a) (in custom ret_assertion at level 0, a constr at level 0, format "$ a").

  Module TestRetNotations.
  Section TestRetNotations.
    Context {reg_t} {R: reg_t -> type} {REnv: Env reg_t} {tau : type}.
    Definition sig: tsig string := [("a", bits_t 1); ("b", bits_t 5)].
    Notation ret_assertion := (@ret_assertion string reg_t R REnv sig tau).
    Notation ret_a_exp := (@ret_a_exp string reg_t R REnv sig tau).
    Notation assertion := (@assertion string reg_t R REnv sig).
    Context (P Q : ret_assertion).
    Context (A B : assertion).
    Context (reg0 : reg_t).

    Notation "'{{' P '}}'" := (P) (at level 10, P custom ret_assertion).

    Definition test1 : ret_assertion := {{ r, True }}.
    Definition test2 : ret_assertion := {{ r, True }}.
    Definition test5 : ret_assertion := {{ r, Γ[b] = Γ[b] }}.
    Definition test6 : ret_assertion := {{ Γ[b] = 5 }}.
    Definition test7 : ret_assertion := {{ $P /\ $Q }}.
    Definition test8 : ret_assertion := {{ `P` /\ (`Q` \/ `P`) }}.
    Definition test9 : ret_assertion := {{ `P` /\ (`Q` \/ ~`P`) \/ Γ[b] = Γ[b]}}.
    Definition test10 : ret_assertion := {{ `fun r env Γ => P r env Γ` /\ $Q }}.
    Definition test11 : ret_assertion := {{ (r, P r env Γ) /\ $Q }}.

  End TestRetNotations.
  End TestRetNotations.

  (* at least level 10 - i assume this is necessary to stay above the application
    of a sigma type `{...} ...`  *)

  Module TestHoareNotation.
  Section TestHoareNotation.
    Context {var_t reg_t ext_fn_t : Type} {R: reg_t -> type} {Sigma: ext_fn_t -> ExternalSignature} {REnv: Env reg_t} {sigma : (∀ f : ext_fn_t, Sig_denote (Sigma f))}.
    Context {sig : tsig var_t} {tau : type}.

    Notation "'{{' P '}}' a '{{' Q '}}'" := (hoare_triple a P Q (sigma := sigma)) (at level 10, P custom assertion, Q custom ret_assertion).

    #[local] Notation action := (TypedSyntax.action unit var_t string R Sigma).
    #[local] Notation acontext := (@TypedSemantics.acontext unit var_t string _ _ R Sigma).
    #[local] Notation assertion := (@assertion var_t reg_t R REnv sig).
    #[local] Notation ret_assertion := (@ret_assertion var_t reg_t R REnv sig tau).
    #[local] Notation a_exp := (@a_exp var_t reg_t R REnv sig).
    #[local] Notation ret_a_exp := (@ret_a_exp var_t reg_t R REnv sig).

    Context (a : action sig tau).
    Context (P P' : assertion) (Q Q': ret_assertion).

    Definition test1 : Prop := {{ `P` }} a {{ `Q` }}.
    Definition test2 : Prop := {{ $P /\ $P' }} a {{ $Q }}.
    Definition test3 : Prop := {{ $P -> $P'}} a {{ $Q \/ ~$Q'}}.

    Context (fn : (bits_t 1) -> (bits_t 1) -> (bits_t 1)).
    Context (e1 e2 e3 : @a_exp (bits_t 1)).

    Definition test4 : Prop := {{ $e1 = $e2 }} a {{ $Q \/ ~$Q'}}.
    (* Definition test5 : Prop := {{ e1 = #fn e2 e3 }} a {{ Q \/ ~Q'}}. *)
    Definition test6 : Prop := {{ $e1 = $e2 }} a {{ $Q \/ ~$Q'}}.

  End TestHoareNotation.
  End TestHoareNotation.
End HoareNotations.

Notation "'hoare(' ass ')'" := (forall env Γ, (ass) env Γ) (ass custom assertion).
Hint Unfold hoare_triple : hoare.

Require Koika.TypedParsing.
Section HoareFacts.
  Import TypedParsing.

  Context {reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.

  #[local] Ltac solve_hoare :=
    repeat match goal with
    | HP: ?P _ _,
    (* | HP: ?P, *)
      HHT: hoare_triple ?a ?P _,
      (* HHT: hoare_triple ?a (fun _ _ => ?P) _, *)
      Hin: interp_action _ _ _ _ _ ?a = Some _ |- _ =>
      specialize (HHT _ _ _ _ _ HP Hin); cbn in HHT
    | HP: ?P _ _,
    (* | HP: ?P, *)
      HHT: hoare_triple_args ?a ?P _,
      (* HHT: hoare_triple_args ?a (fun _ _ => ?P) _, *)
      Hin: interp_args _ _ _ _ _ ?a = Some _ |- _ =>
      specialize (HHT _ _ _ _ _ HP Hin); cbn in HHT
    | H: ?Q ?r (commit_update _ (_ ?l log_empty)) ?G |-
          ?Q ?r (commit_update _ ?l) ?G => now rewrite log_app_empty_l in H
    | HHT: hoare_triple ?a ?P ?Q,
      HP: ?P (commit_update ?env ?al) ?c,
      Hin: interp_action ?env _ _ log_empty ?al ?a = Some _ |- _ =>
      rewrite <- (log_app_empty_l al) in HP;
      pose_once (hoare_log_irr _ _ _ HHT  _ _ _ _ _ _ _ HP Hin)
    | |- hoare_triple _ _ _ => unfold hoare_triple
    | |- context[commit_update _ log_empty] => rewrite commit_update_empty
    | H: context [(fun _ => _) _] |- _ => progress (cbv beta in H)
    | H: exists _, _ |- _ => destruct H
    | _ => progress simpl_hoare
    | _ => progress intros
    | _ => solve [eauto with hoare]
    end.

  #[local] Notation action := (TypedSyntax.action unit string string R Sigma).
  #[local] Notation acontext := (@TypedSemantics.acontext unit string string _ _ R Sigma).

  Section sigma.
    Context {sigma : (∀ f : ext_fn_t, Sig_denote (Sigma f))}.
    Context `{FiniteType reg_t}.
    #[local] Notation "'{{' P '}}' a '{{' Q '}}'" := (@hoare_triple _ _ _ R Sigma REnv _ _ sigma a P Q) (at level 10, P custom assertion, Q custom ret_assertion).
    (* #[local] Notation "'{{' P '}}' a '{{' Q '}}'" := (@hoare_triple _ _ R Sigma REnv _ _ sigma P a Q) (at level 10). *)

    Theorem hoare_post_true {sig tau} :
      ∀ P (a : action sig tau),
      {{ $P }} a {{ True }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_pre_false {sig tau} :
      ∀ Q (a : action sig tau),
      {{ False }} a {{ $Q }}.
    Proof. solve_hoare. Qed.

    (* as the name signifies this rule is intended for backwards reasoning *)
    Theorem hoare_weaken_pre {sig tau} :
      ∀ P P' Q (a : action sig tau),
      {{ $P' }} a {{ $Q }} ->
      hoare( $P -> $P' ) ->
      {{ $P }} a {{ $Q }}.
    Proof. solve_hoare. Qed.

    (* as the name signifies this rule is intended for backwards reasoning *)
    Theorem hoare_weaken_pre_ex {sig tau} :
      ∀ P Q (a : action sig tau),
      (exists P', {{ $P' }} a {{ $Q }} /\
      hoare( $P -> $P' )) ->
      {{ $P }} a {{ $Q }}.
    Proof. solve_hoare. Qed.

    (* as the name signifies this rule is intended for backwards reasoning *)
    Theorem hoare_strengthen_post {sig tau} :
      ∀ P Q Q' (a : action sig tau),
      {{ $P }} a {{ $Q' }} ->
      (forall ret env Γ, Q' ret env Γ -> Q ret env Γ) ->
      {{ $P }} a {{ $Q }}.
    Proof. solve_hoare. Qed.

    (* A combination of both rules *)
    Theorem hoare_consequence {sig tau} :
      ∀ P P' Q Q' (a : action sig tau),
      {{ $P' }} a {{ $Q' }} ->
      hoare( $P -> $P' ) ->
      (forall ret env Γ, Q' ret env Γ -> Q ret env Γ) ->
      {{ $P }} a {{ $Q }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_fail {sig} tau :
      ∀ Q,
      {{ True }} (Fail tau : action sig _) {{ $Q }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_var {sig tau} {k} (m : member (k,tau) _) :
      ∀ Q,
      {{ Q (cassoc m Γ) env Γ }} (Var m : action sig tau) {{ $Q }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_const {sig tau} (cst : type_denote tau) :
      ∀ Q,
      {{ Q cst env Γ }} (Const cst : action sig tau) {{ $Q }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_assign {sig tau} {k} (m : member (k,tau) _) (exp : action sig tau) :
      ∀ P Q,
      {{ $P }} exp {{ `fun r env Γ => Q Ob env (creplace m r Γ)` }} ->
      {{ $P }} (Assign m exp) {{ $Q }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_seq  {sig tau} c1 (c2 : action sig tau) :
      ∀ P Q R,
      {{ $Q }} c2 {{ $R }} →
      {{ $P }} c1 {{ $Q }} →
      {{ $P }} <{ `c1`; `c2` }> {{ $R }}.
    Proof. solve_hoare. Qed.

    (* Γ[v ↦ exp] == CtxCons (v, _) val_of_expr Γ *)
    Theorem hoare_bind {sig tau tau'} v (exp : action sig tau') (body : action _ tau) :
      ∀ P Q R,
      {{ $Q }} body {{ `fun r env Γ => R r env (ctl Γ)` }} ->
      {{ $P }} exp {{ `fun r env Γ => Q env (CtxCons (v, tau') r Γ)` }} ->
      {{ $P }} (Bind v exp body) {{ $R }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_if {sig tau} (c : action sig (bits_t 1)) (tr fl : action sig tau) :
      ∀ P Qtr Qfl R,
      {{ $Qfl }} fl {{ $R }} ->
      {{ $Qtr }} tr {{ $R }} ->
      {{ $P }} c {{ `fun r env Γ => if Bits.single r then Qtr env Γ else Qfl env Γ` }} ->
      {{ $P }} <{if `c` then `tr` else `fl`}> {{ $R }}.
    Proof. solve_hoare; rewrite Heqb in H2; solve_hoare. Qed.

    Theorem hoare_read {sig} port reg :
      ∀ Q,
      {{ Q env[reg] env Γ }} (Read port reg : action sig _) {{ $Q }}.
    Proof. solve_hoare;
      rewrite commit_read, commit_update_empty by easy; solve_hoare.
      now rewrite latest_write0_empty in Heqo0.
    Qed.

    Theorem hoare_write {sig} port reg exp :
      ∀ P Q,
      {{ $P }} exp {{ `fun ret env Γ => Q Ob (REnv.(putenv) env reg ret) Γ` }} ->
      {{ $P }} (Write port reg exp: action sig _) {{ $Q }}.
    Proof. solve_hoare; now rewrite commit_write. Qed.

    Theorem hoare_unop {sig} fn (a1 : action sig _) :
      ∀ P Q,
      {{ $P }} a1 {{ `fun r env Γ => Q ((PrimSpecs.sigma1 fn) r) env Γ` }} ->
      {{ $P }} (Unop fn a1) {{ $Q }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_binop {sig} fn a1 (a2 : action sig _) :
      ∀ P R,
      {{ $P }} a1 {{ `fun r1 env Γ =>
        exists Q,
        {{ $Q }} a2 {{ `fun r2 env Γ => R ((PrimSpecs.sigma2 fn) r1 r2) env Γ` }}
        /\ Q env Γ `
      }} ->
      {{ $P }} (Binop fn a1 a2) {{ $R }}.
    Proof. solve_hoare. Qed.

    #[deprecated(note="This typically results in scoping issues within proofs - it is only kept for completeness - consider using hoare_binop instead")]
    Theorem hoare_binop' {sig} fn a1 (a2 : action sig _) r1 :
      ∀ P Q R,
      {{ $Q }} a2 {{ `fun r2 env Γ => R ((PrimSpecs.sigma2 fn) r1 r2) env Γ` }} ->
      {{ $P }} a1 {{ `fun r env Γ => r1 = r /\ Q env Γ` }} ->
      {{ $P }} (Binop fn a1 a2) {{ $R }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_apos {sig tau} pos (a : action sig tau):
      ∀ P Q,
      {{ $P }} a {{ $Q }} ->
      {{ $P }} (APos pos a) {{ $Q }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_int_call {sig tau} {argspec : tsig var_t} (fn : InternalFunction' string (action argspec tau)) (args : acontext sig argspec) :
      ∀ P R,
      hoare_triple_args args P (fun rs env Γ' =>
        exists Q,
        {{ $Q }} fn {{ `fun r env _ => R r env Γ'` }}
        /\ Q env rs
      ) (sigma := sigma)  ->
      {{ $P }} (InternalCall fn args) {{ $R }}.
    Proof. solve_hoare. Qed.

    #[deprecated(note="This typically results in scoping issues within proofs - it is only kept for completeness - consider using hoare_int_call instead")]
    Theorem hoare_int_call' {sig tau} {argspec : tsig var_t} (fn : InternalFunction' string (action argspec tau)) (args : acontext sig argspec) Γ' :
      ∀ P Q R,
      {{ $Q }} fn.(int_body) {{ `fun r env Γ => R r env Γ'` }} ->
      hoare_triple_args args P (fun rs env Γ => Q env rs /\ Γ' = Γ ) (sigma := sigma)  ->
      {{ $P }} (InternalCall fn args) {{ $R }}.
    Proof. solve_hoare. Qed.

    Theorem hoare_args_cons {sig k_tau} {argspec : tsig var_t} (args : acontext sig argspec) (arg : action _ (snd k_tau)) :
      ∀ P R,
      hoare_triple_args args P (fun rs env Γ =>
        exists Q,
        {{ $Q }} arg {{ `fun r env Γ => R (CtxCons (k_tau) r rs) env Γ` }}
        /\ Q env Γ
      ) (sigma := sigma) ->
      hoare_triple_args (CtxCons (k_tau) arg args) P R (sigma := sigma).
    Proof. intros * Hargs. unfold hoare_triple_args. intros * HP Hin. cbn in Hin.
      simpl_hoare.
      specialize (Hargs _ _ _ _ _ HP Heq).
      destruct Hargs as [Q [? ?]]; subst.
      rewrite <- (log_app_empty_l l) in H1.
      pose proof (hoare_log_irr _ _ _ H0 _ _ _ _ _ _ _ H1 Heq0).
      cbn in H2.
      now rewrite log_app_empty_l in H2.
    Qed.

    (* should probably be deprecated *)
    #[deprecated(note="This typically results in scoping issues within proofs - it is only kept for completeness - consider using hoare_args_cons instead")]
    Theorem hoare_args_cons' {sig k_tau} {argspec : tsig var_t} (args : acontext sig argspec) (arg : action _ (snd k_tau)) rs' :
      ∀ P Q R,
      {{ $Q }} arg {{ `fun r env Γ => R (CtxCons (k_tau) r rs') env Γ` }} ->
      hoare_triple_args args P (fun rs env Γ => Q env Γ /\ rs' = rs ) (sigma := sigma) ->
      hoare_triple_args (CtxCons (k_tau) arg args) P R (sigma := sigma).
    Proof. intros * Harg Hargs. unfold hoare_triple_args. intros * HP Hin. cbn in Hin.
      simpl_hoare.
      specialize (Hargs _ _ _ _ _ HP Heq).
      destruct Hargs; subst.
      rewrite <- (log_app_empty_l l) in H0.
      pose proof (hoare_log_irr _ _ _ Harg _ _ _ _ _ _ _ H0 Heq0).
      cbn in H1.
      now rewrite log_app_empty_l in H1.
    Qed.

    Theorem hoare_args_empty {sig} :
      ∀ (P : tcontext [] → REnv.(env_t) R → @tcontext var_t sig → Prop),
      hoare_triple_args CtxEmpty (fun env Γ => P CtxEmpty env Γ) P (sigma := sigma).
    Proof. intros *; unfold hoare_triple_args. solve_hoare. Qed.

    Theorem hoare_args_weaken_pre {sig} {argspec : tsig var_t} (args : acontext sig argspec) :
    ∀ P P' Q,
    hoare_triple_args args P' Q (sigma := sigma) (REnv := REnv)->
    (∀ env Γ,  P env Γ -> P' env Γ) ->
    hoare_triple_args args P Q (sigma := sigma) (REnv := REnv).
    Proof. unfold hoare_triple_args in *. intros. exact (H0 _ _ _ _ _ (H1 _ _ H2) H3). Qed.
  End sigma.

  Theorem hoare_ext_call {sig} sigma fn a :
    ∀ P Q,
    hoare_triple a P (fun r env Γ => Q (sigma fn r) env Γ) (sigma := sigma) (REnv := REnv) ->
    hoare_triple (ExternalCall fn a : action sig _) P Q (sigma := sigma) (REnv := REnv).
  Proof. solve_hoare. Qed.

End HoareFacts.

Require Import Koika.Frontend.

Require Import Koika.TypedParsing.
Inductive empty_reg_t :=.
Definition empty_R (r : empty_reg_t) : type := match r with end.

Definition min : function empty_R empty_Sigma := <{
fun min (a : bits_t 5) (b : bits_t 5) : bits_t 5 =>
  if (a < b)
    then a
    else b
}>.

Open Scope nat_scope.

Ltac hoare_weaken_pre in_p :=
  match goal with
  | |- hoare_triple ?a ?P ?Q => not_evar P;
    eapply (hoare_weaken_pre P _ Q a);
    [|intros in_p]
  end.

Ltac hoare_step :=
  lazymatch goal with
  | |- hoare_triple (Fail _) _ ?Q             => apply hoare_fail
  | |- hoare_triple (Var _) _ ?Q              => apply hoare_var
  | |- hoare_triple (Const _) _ ?Q            => apply hoare_const
  | |- hoare_triple (Assign _ _) _ ?Q         => eapply hoare_assign
  | |- hoare_triple (Seq _ _) _ ?R            => eapply hoare_seq
  | |- hoare_triple (Bind _ _ _) _ ?R         => eapply hoare_bind
  | |- hoare_triple (If _ _ _) _ ?R           => eapply hoare_if
  | |- hoare_triple (Read _ ?idx) _ ?Q        => apply (hoare_read _ idx _)
  | |- hoare_triple (Write _ ?idx _) _ ?Q     => eapply (hoare_write _ idx _ _ _)
  | |- hoare_triple (Unop ?fn _) _ _          => eapply (hoare_unop fn)
  | |- hoare_triple (Binop ?fn _ _ ) _ _      => eapply (hoare_binop fn)
  | |- hoare_triple (ExternalCall ?fn _) _ ?Q => eapply (hoare_ext_call _ fn)
  | |- hoare_triple (InternalCall ?fn _) _ ?R => eapply (hoare_int_call fn)
  | |- hoare_triple (APos _ _) - ?Q           => eapply hoare_apos
  | |- hoare_triple_args CtxEmpty _ ?P        => apply hoare_args_empty
  | |- hoare_triple_args (CtxCons _ _ _) _ ?R => eapply hoare_args_cons
  | |- _ => eexists; apply conj
  end.

Ltac hoare_cleanup :=
  repeat match goal with
  | |- context[TypedParsing.refine_sig_tau] => unfold TypedParsing.refine_sig_tau
  | |- context[action_of_function ?f]          => progress change (action_of_function f) with (int_body f)
  | |- context[int_body {| int_body := ?b |}]  => progress change (int_body {| int_body := b |}) with b
  | |- context[a_exp_of_type _ _ _]            => progress change (a_exp_of_type ?t _ _) with t
  | H: context[a_exp_of_type _ _ _]       |- _ => progress change (a_exp_of_type ?t _ _ ) with t in H
  | |- context[@nat_to_type (bits_t _) _]      => progress change (@nat_to_type (bits_t ?sz) ?n) with (Bits.of_nat sz n)
  | H: context[@nat_to_type (bits_t _) _] |- _ => progress change (@nat_to_type (bits_t ?sz) ?n) with (Bits.of_nat sz n) in H
  | |- (fun _ => _) _ _ _ => hnf
  | |- (fun _ => _) _ _ => hnf
  | H: (fun _ => _) _ _ _ |- _ => hnf in H
  | H: (fun _ => _) _ _ |- _ => hnf in H
  | |- context[PrimSpecs.sigma1] => unfold PrimSpecs.sigma1
  | |- context[PrimSpecs.sigma2] => unfold PrimSpecs.sigma2
  | |- context[CircuitPrimSpecs.sigma1] => unfold CircuitPrimSpecs.sigma1
  | |- context[CircuitPrimSpecs.sigma2] => unfold CircuitPrimSpecs.sigma2

  | |- context[PrimSignatures.Sigma1] => unfold PrimSignatures.Sigma1
  | |- context[PrimSignatures.Sigma2] => unfold PrimSignatures.Sigma2
  | |- context[CircuitSignatures.CSigma1] => unfold CircuitSignatures.CSigma1
  | |- context[CircuitSignatures.CSigma2] => unfold CircuitSignatures.CSigma2
  | |- context[Sig_of_CSig] => unfold Sig_of_CSig
  | |- context[snd (pair ?a ?b)]      => progress change (snd (pair a b)) with b
  | H: context[snd (pair ?a ?b)] |- _ => progress change (snd (pair a b)) with b in H
  | |- context[var_ctx_member]        => unfold var_ctx_member
  | H: context[var_ctx_member]   |- _ => unfold var_ctx_member in H
  | |- context[VarCtxMemberHd]        => unfold VarCtxMemberHd
  | H: context[VarCtxMemberHd]   |- _ => unfold VarCtxMemberHd in H
  | |- context[VarCtxMemberTl]        => unfold VarCtxMemberTl
  | H: context[VarCtxMemberTl]   |- _ => unfold VarCtxMemberTl in H
  | |- context[Hoare.var_ctx_member]        => unfold Hoare.var_ctx_member
  | H: context[Hoare.var_ctx_member]   |- _ => unfold Hoare.var_ctx_member in H
  | |- context[Hoare.VarCtxMemberHd]        => unfold Hoare.VarCtxMemberHd
  | H: context[Hoare.VarCtxMemberHd]   |- _ => unfold Hoare.VarCtxMemberHd in H
  | |- context[Hoare.VarCtxMemberTl]        => unfold Hoare.VarCtxMemberTl
  | H: context[Hoare.VarCtxMemberTl]   |- _ => unfold Hoare.VarCtxMemberTl in H
  | |- context[cassoc (MemberHd _ _) (CtxCons _ _ _)]          => progress change (cassoc (MemberHd _ _) (CtxCons _ ?a _)) with a
  | H: context[cassoc (MemberHd _ _) (CtxCons _ _ _)]     |- _ => progress change (cassoc (MemberHd _ _) (CtxCons _ ?a _)) with a in H
  | |- context[cassoc (MemberTl _ _ _ _) (CtxCons _ _ _)]      => progress change (cassoc (MemberTl _ _ _ ?m) (CtxCons _ _ ?ctx)) with (cassoc m ctx)
  | H: context[cassoc (MemberTl _ _ _ _) (CtxCons _ _ _)] |- _ => progress change (cassoc (MemberTl _ _ _ ?m) (CtxCons _ _ ?ctx)) with (cassoc m ctx) in H
  (* clean type of context references (else setoid_rewrite is necessary) *)
  | |- context[argSigs {| argSigs := _ |}] => progress change (argSigs {| argSigs := ?a |}) with a
  | |- context[vect_hd (vect_cons _ _)]    => progress change (vect_hd (vect_cons ?a _)) with a
  | |- context[vect_tl (vect_cons _ _)]    => progress change (vect_tl (vect_cons _ ?v)) with v
  | |- context[vect_map _ (vect_cons _ _)] => progress change (vect_map ?fn (vect_cons ?a ?v')) with (vect_cons (fn a) (vect_map fn v'))
  (* typical hypothesis cleanup *)
  | H: ?A = ?A |- _ => clear H
  | H: prod _ _ |- _ => destruct H
  | H: and _ _ |- _ => destruct H as [?H ?H]
  | H: Some _ = Some _ |- _ => apply Some_inj in H
  | H: pair _ _ = pair _ _ |- _ => apply pair_inj in H
  end.

(* TODO: here is still a lot of Notation and coercion cleanup - this should be organized a bit cleaner *)
Ltac hoare' in_p :=
  hoare_cleanup;
  try match goal with
  | |- hoare_triple (int_body ?a) _ _ => first [head_constructor a | let h := head a in unfold h] (* function *)
  | |- hoare_triple           ?a  _ _ => first [head_constructor a | let h := head a in unfold h] (* action *)
  end;
  hoare_cleanup;
  try hoare_weaken_pre in_p;
  repeat (hoare_step; hoare_cleanup);
  hoare_cleanup;
  (* improve redability by folding coercion back *)
  repeat match goal with
  | |- context[int_body ?f] => change (int_body f) with (action_of_function f)
  end.

Tactic Notation "hoare" "as" "[" simple_intropattern_list(p1) "|" simple_intropattern_list(p2) "]" :=
  intros p1; hoare' p2.
Tactic Notation "hoare" "as" "[" simple_intropattern_list(p) "]" :=
  intros; hoare' p.

Tactic Notation "hoare" :=
  hoare as [?env ?Γ ?H].

Notation "'{' P '}' a '{' Q '}'" := (hoare_triple a P Q) (at level 200, P custom assertion, Q custom ret_assertion, only printing).

Notation "G '?[' f ']'" := (@cassoc _ _ _ (f,_) _ G) (at level 1, only printing).
Notation "'bits(' n ')'" := (Bits.of_nat _ n) (format "bits( n )", only printing).


Module HoareTest.

  Inductive reg_t :=
    | r0
    | r1
    .

  Definition logsz := 4.
  Definition sz := (pow2 logsz). (* Fancy for [2^4]. *)

  (*! [r0] is a register storing 2^4 = 16 bits: !*)
  Definition R reg :=
    match reg with
    | r0 => bits_t sz
    | r1 => bits_t sz
    end.


  Program Definition isodd_typed : function R empty_Sigma := <{
    fun isodd_typed (bs: R r0) : bits_t 1 =>
      bs[0b"0000"]
  }>.
  Program Definition divide_typed : TypedParsing.action R empty_Sigma := <{
    let v := read0(r0) in
    if !isodd_typed(v) then
      write0(r1, v >> Ob~1)
    else
      write0(r1, v)
  }>.

  Definition double {sz : nat} : function R empty_Sigma := <{
  fun double (a: bits_t sz) : bits_t sz =>
    a << Ob~1
  }>.

  Definition add (sz : nat) : function R empty_Sigma := <{
  fun add (a: bits_t sz) (b: bits_t sz) : bits_t sz =>
    a + b
  }>.

  Definition add_double (sz : nat) : function R empty_Sigma := <{
  fun add (a: bits_t sz) (b: bits_t sz) : bits_t sz =>
    a + double(b)
  }>.

  Definition times_three (sz : nat) : function R empty_Sigma :=
    <{ fun times_three (b: bits_t sz) : bits_t sz =>
         (b << Ob~1) + b }>.

  Notation "'{{' P '}}' a '{{' Q '}}'" := (forall REnv, @hoare_triple _ _ _ R empty_Sigma REnv _ _ empty_sigma a P Q) (at level 10, P custom assertion, Q custom ret_assertion, only parsing).

  Theorem times_three_correct :
    ∀ sz n : nat,
    {{ Γ[b] = n }} times_three sz {{ r, r = $(3*n) }}.
  Proof.
    hoare.
    cbv zeta.
    unfold BitFuns.lsl.
    vm_compute (Bits.to_nat _).
    setoid_rewrite H.
    rewrite <- Nat2Bits.inj_lsl_pow2.
    rewrite <- Nat2Bits.inj_add.
    f_equal.
    cbn. lia.
  Qed.

  (* Theorem add_8_self :
    ∀ n REnv (env : REnv.(env_t) R) action_log scheduler_log ,
    let Γ := (CtxCons ("a", bits_t 8) (Bits.of_nat 8 n)
      (CtxCons ("b", bits_t 8) (Bits.of_nat 8 n) CtxEmpty)) in
    match interp_action env empty_sigma Γ scheduler_log action_log (add 8) with
    | Some (_, r ,_) => r = Bits.of_nat _ (2*n)
    | None => False
    end.
  Proof.
    intros. cbn.
    now rewrite Nat.add_0_r, Nat2Bits.inj_add.
  Qed. *)

  (* Theorem double_correct :
    ∀ sz n REnv (env : REnv.(env_t) R) action_log scheduler_log ,
    let Γ := (CtxCons ("a", bits_t sz) (Bits.of_nat sz n) CtxEmpty) in
    forall l r G,
    interp_action env empty_sigma Γ scheduler_log action_log (@double sz) = Some (l,r,G) ->
    r = Bits.of_nat _ (2*n).
  Proof.
    intros.
    unfold action_of_function, int_body, double, TypedParsing.refine_sig_tau in H.
    interp_action_all_t.
    unfold interp_action, opt_bind, no_latest_writes in *;
    repeat log_cleanup_step.
    unfold PrimSpecs.sigma2, CircuitPrimSpecs.sigma2, BitFuns.lsl.
    vm_compute (Bits.to_nat _).
    simpl (cassoc _ _).
    now rewrite <- Nat2Bits.inj_lsl_pow2, Nat.pow_1_r, Nat.mul_comm.
  Qed. *)

  (* Theorem add_double_triple :
    ∀ sz n REnv (env : REnv.(env_t) R) action_log scheduler_log ,
    let Γ := (CtxCons ("a", bits_t sz) (Bits.of_nat sz n) (CtxCons ("b", bits_t sz) (Bits.of_nat sz n) CtxEmpty)) in
    forall l r G,
    interp_action env empty_sigma Γ scheduler_log action_log (add_double sz) = Some (l,r,G) ->
    r = Bits.of_nat _ (3*n).
  Proof.
    intros.
    unfold action_of_function, int_body, add_double, TypedParsing.refine_sig_tau in H.
    interp_action_all_t.
    unfold interp_action, opt_bind, no_latest_writes in *;
    repeat log_cleanup_step.
    fold interp_action in H. EXPLODES + CANNOT HANDLE interp_args *)

  (* Theorem add_self' :
    ∀ sz n REnv (env : REnv.(env_t) R) action_log scheduler_log ,
    let Γ := (CtxCons ("a", bits_t sz) (Bits.of_nat sz n) (CtxCons ("b", bits_t sz) (Bits.of_nat sz n) CtxEmpty)) in
    forall l r G,
    interp_action env empty_sigma Γ scheduler_log action_log (add sz) = Some (l,r,G) ->
    r = Bits.of_nat _ (2*n).
  Proof.
    intros.
    unfold add in H.
    unfold action_of_function in H.
    unfold int_body in H.
    unfold TypedParsing.refine_sig_tau in H.
    interp_action_all_t.

    unfold interp_action, opt_bind, no_latest_writes in *;
    repeat log_cleanup_step.
    cbn.
    now rewrite Nat.add_0_r, Nat2Bits.inj_add.
  Qed. *)


  Theorem double_correct :
    ∀ sz n : nat,
    {{ Γ[a] = n }} @double sz {{ r, r = $(2*n) }}.
  Proof.
    hoare.
    unfold BitFuns.lsl.
    vm_compute (Bits.to_nat _).
    now rewrite H, <- Nat2Bits.inj_lsl_pow2, Nat.pow_1_r, Nat.mul_comm.
  Qed.

  Ltac hoare_apply a :=
    eapply (hoare_strengthen_post _ _ _ _ ltac:(apply a));
    intros; hoare_cleanup.


  Theorem add_double_correct :
    ∀ sz n : nat,
    {{ Γ[a] = n /\ Γ[b] = n }} @add_double sz {{ r, r = $(3*n) }}.
  Proof.
    intros.
    hoare.
    hoare_apply double_correct.
    rewrite H1, H, <- Nat2Bits.inj_add. reflexivity.

    hoare_cleanup.
    assumption.
  Qed.
  (* Print add_double_correct. *)

  Theorem add_self :
    ∀ sz n : nat,
    {{ Γ[a] = n /\ Γ[b] = n }} add sz {{ r, r = $(2*n) }}.
  Proof.
    hoare.
    simpl (2*n).
    now rewrite H, H0, <- Nat2Bits.inj_add, Nat.add_0_r.
  Qed.

  Lemma assert_r01' {v0 v1 : nat} :
    Nat.Even v0 ->
    v0 < 2^sz ->
    {{ env[r0] = v0 /\ env[r1] = v1 }}
    (divide_typed)
    {{ r, env[r0] = v0 /\ env[r1] = $(v0/2) }}.
  Proof.
    hoare.
    hoare.
    eexists; apply conj.
    (* match goal with
    | |- hoare_triple (rew [λ t : ?A, ?P] ?e in ?k) _ _ => unfold e, eq_rect
    end. *)
    hoare.
    hnf.
    change (bin_string_to_N ?s) with ltac:(let e := eval cbn in (bin_string_to_N s) in exact (e)).
    change (TypedParsing.len ?s) with ltac:(let e := eval cbn in (TypedParsing.len s) in exact (e)).

    (* unfold BitFuns.sel. *)
    unfold BitFuns.sel.
    simpl (Bits.single _).
    rewrite H1.

    repeat match goal with
    | H: context[@nat_to_type ?t ?n] |- _ =>
      let t' := eval cbn in t in
      match t' with
      | bits_t ?sz =>
        change (@nat_to_type t n) with (Bits.of_nat sz n) in H
      end
    | |- context[@nat_to_type ?t ?n] =>
      let t' := eval cbn in t in
      match t' with
      | bits_t ?sz =>
        change (@nat_to_type t n) with (Bits.of_nat sz n)
      end
    end.

    change (@vect_hd _ ?sz (Bits.of_nat _ ?v)) with (vect_hd (Bits.of_nat (S sz) v)).
    rewrite Nat2Bits.hd_odd.
    rewrite Nat.negb_odd.
    apply Nat.even_spec in H.
    rewrite H.
    eexists; apply conj.
    hoare.
    hoare_cleanup.
    rewrite ?get_put_eq.
    rewrite ?get_put_neq.
    split.
    assumption.
    unfold BitFuns.lsr.
    vm_compute (Bits.to_nat _).
    rewrite <- Nat2Bits.inj_lsr_pow2.
    rewrite Nat.mod_small.
    reflexivity.
    assumption.
    inversion 1.
  Qed.

(* Lemma min_correct m n REnv:
  hoare_triple (sigma := empty_sigma) (REnv := REnv)

  min.(int_body)
  (* (Γ.[ a ] = (a_exp_of_const (Bits.of_nat 5 m)) /\ Γ.[ b ] = Bits.of_nat 5 n) *)
  (fun _env Γ => Γ[a] = Bits.of_nat 5 m /\ Γ[b] = Bits.of_nat 5 n)
  (fun r _env _Γ => r = if m <? n then Bits.of_nat 5 m else Bits.of_nat 5 n).
Proof.
  unfold hoare_triple'.
  unfold min, int_body.
  unfold TypedParsing.refine_sig_tau.
  hoare_step.
  hoare_step.
  hoare_step.

  hoare_step.

  (* apply hoare_binop. *)

  match goal with
  (* | |- hoare_triple ?P _ _ => apply (hoare_binop _ _ _ _ P) *)
  | |- hoare_triple _ (Binop ?fn ?a1 ?a2) ?R      => eapply (hoare_binop fn a1 a2 _ _ _ R)
  end.
  eapply hoare_binop.

  hoare_step.
  hoare_step.
  hoare.
  eapply hoare_binop.
  hoare_step.
  unfold convert_ctx, id; intros env Γ H. destruct H. rewrite ?H, ?H0. split. reflexivity.
  simpl (arg2Sig _).
  rewrite H0.
  simpl (Bits.single _).
Admitted. *)


  Section switching.
    Context {pos_t var_t fn_name_t : Type} {reg_t ext_fn_t} {R: reg_t -> type} {Sigma: ext_fn_t -> ExternalSignature}.
    (* Context {sig : tsig var_t}. *)
    (* Context {tau : type}. *)
    (* Context {REnv: Env reg_t}. *)

    (* Context {sig}. *)

  Notation action := (TypedSyntax.action pos_t var_t fn_name_t R Sigma).

  Section measure.
    (* Note: measure is only declared as typeclass to improve readability.
        implementations should not be declared as instances to avoid accidental
        confusions *)
    Class measure := {
      measure_fn : forall {sig tau}, action sig tau -> nat;
      measure_default : nat;
      measure_acc : nat -> nat -> nat;
    }.

    Definition ext_measure := ext_fn_t -> nat.
    Existing Class ext_measure.

    (* todo *)
    (* Instance empty_ext_measure : ext_measure  *)

    Notation meas s t := (@measure_fn _ s t).
    Notation "a '&m' b" := (measure_acc a b) (at level 40).
    (* Notation "a '|m' b" := (measure_acc _ a b) (at level 50). *)

    Definition measure_action_args (m : measure) (em : ext_measure) :=
      @action_rect_complete pos_t var_t fn_name_t reg_t ext_fn_t R Sigma
      (fun _ _ a => nat) (fun _ _ args => nat)
      (* actions *)
      (fun s t                         => meas s t (Fail t))
      (fun s k t mem                   => meas s t (Var mem))
      (fun s t c                       => meas s t (Const c))
      (fun s k t mem ex rex            => meas s _ (Assign mem ex) &m rex)
      (fun s t a1 a2 ra1 ra2           => meas s t (Seq a1 a2) &m ra1 &m ra2)
      (fun s _ t var ex body rex rbody => meas s t (Bind var ex body) &m rex &m rbody)
      (fun s t c tr fl rc rt rf        => meas s t (If c tr fl) &m rc &m rt &m rf)
      (fun s p idx                     => meas s _ (Read p idx))
      (fun s p idx val rv              => meas s _ (Write p idx val) &m rv)
      (fun s fn a1 ra1                 => meas s _ (Unop fn a1) &m ra1)
      (fun s fn a1 a2 ra1 ra2          => meas s _ (Binop fn a1 a2) &m ra1 &m ra2)
      (fun s fn a ra                   => meas s _ (ExternalCall fn a) &m ra &m (em fn))
      (fun s _ _ fn args rbody rargs   => meas s _ (InternalCall fn args) &m rargs &m rbody)
      (fun s t p a ra                  => meas s t (APos p a) &m ra)
      (* args *)
      (* CtxEmpty *)(fun s                         => m.(measure_default))
      (* CtxCons  *)(fun s k t asc a args ra rargs => m.(measure_acc) ra rargs).

    Definition measure_action (m : measure) (em : ext_measure) :=
      fst (measure_action_args m em).

    Definition measure_args (m : measure) (em : ext_measure) :=
      snd (measure_action_args m em).

  End measure.

  Definition term_size : measure := {|
    measure_fn := fun _ _ a => 1;
    measure_default := 0;
    measure_acc := Nat.add;
  |}.


  Fixpoint muxtree {sig tau} {sz} (bit_idx : nat) (k: var_t) {m : member (k, bits_t sz) sig} {bsz} (bodies: bits bsz -> action sig tau) :=
    match bsz return (bits bsz -> action sig tau) -> action sig tau with
    | 0 => fun bodies => bodies Ob
    | S n => fun bodies =>
      (* FIXME add a version of sel taking a compile-time constant? *)
      If (Binop (Bits2 (Sel _)) (Var m) (Const bit_idx))
         (muxtree (S bit_idx) k (fun bs => bodies bs~1) (m := m))
         (muxtree (S bit_idx) k (fun bs => bodies bs~0) (m := m))
    end bodies.

  Definition CompleteMuxTree {sig tau} {sz} (k: var_t) {m : member (k, bits_t sz) sig} (branches: bits sz -> action sig tau) :=
    muxtree 0 k branches (m := m).

  Lemma mux_tree_size_bounded :
    ∀ ext_meas sig tau sz k m b,
    ∃ n sz0, ∀ sz', sz' >= sz0 -> sz' = sz -> (* big O definition *)
    measure_action term_size ext_meas _ _ (@CompleteMuxTree sig tau sz k m b) < sz^2 *n.
  Proof.
    intros ext_meas.
    intros sig tau sz k m b.
    eexists.
    eexists 1.
    intros ? H ->.

    induction sz.
    - inversion H.
    - destruct sz0.
      + unfold CompleteMuxTree, muxtree. simpl.
      rewrite Nat.add_0_r.

        (* apply Nat.lt_succ_diag_r. *)
        (* cbn. *)
        (* unfold measure_action. unfold measure_action_args, fst. cbn. *)
        (* fold measure_action_args. *)
        (* rewrite Nat.add_0_r. *)
        (* Search (_ < S _). *)
        (* apply Nat.lt_succ_diag_r. *)
      (* simpl (0 ^ 2). *)
    (* cbn. *)
  Admitted.
  End switching.

End HoareTest.
