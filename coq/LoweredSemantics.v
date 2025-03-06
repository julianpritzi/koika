(*! Language | Semantics of Lowered Kôika programs !*)
Require Export Koika.Common Koika.Environments Koika.Syntax Koika.TypedSemantics Koika.LoweredSyntax.

Section Interp.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> nat}.
  Context {Sigma: ext_fn_t -> CExternalSignature}.

  Context {REnv: Env reg_t}.

  Notation Log := (CLog R REnv).

  Notation rule := (rule pos_t var_t R Sigma).
  Notation action := (action pos_t var_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Definition lcontext (sig: lsig) :=
    context Bits.bits sig.

  Section Action.
    Context (r: REnv.(env_t) (fun idx => bits (R idx))).
    Context (sigma: forall f, CSig_denote (Sigma f)).

    Fixpoint interp_action
             {sig: lsig}
             {sz}
             (Gamma: lcontext sig)
             (sched_log: Log)
             (action_log: Log)
             (a: action sig sz)
    : option (Log * bits sz * (lcontext sig)) :=
      match a in LoweredSyntax.action _ _ _ _ ts sz return (lcontext ts -> option (Log * bits sz * (lcontext ts)))  with
      | Fail sz => fun _ =>
        None
      | Var k m => fun Gamma =>
        Some (action_log, cassoc m Gamma, Gamma)
      | Const cst => fun Gamma =>
        Some (action_log, cst, Gamma)
      | Seq r1 r2 => fun Gamma =>
        let/opt3 action_log, _, Gamma := interp_action Gamma sched_log action_log r1 in
        interp_action Gamma sched_log action_log r2
      | Assign k m ex => fun Gamma =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log ex in
        Some (action_log, Ob, creplace m v Gamma)
      | @Bind _ _ _ _ _ _ sig _ sz sz' ex body => fun (Gamma : lcontext sig) =>
        let/opt3 action_log1, v, Gamma := interp_action Gamma sched_log action_log ex in
        let/opt3 action_log2, v, Gamma := interp_action (CtxCons sz v Gamma) sched_log action_log1 body in
        Some (action_log2, v, ctl Gamma)
      | If cond tbranch fbranch => fun Gamma =>
        let/opt3 action_log, cond, Gamma := interp_action Gamma sched_log action_log cond in
        if Bits.single cond then
          interp_action Gamma sched_log action_log tbranch
        else
          interp_action Gamma sched_log action_log fbranch
      | Read prt idx => fun Gamma =>
        if may_read sched_log action_log prt idx then
          Some (log_cons idx (LE LogRead prt tt) action_log,
                match prt with
                | P0 => REnv.(getenv) r idx
                | P1 => match latest_write0 (log_app action_log sched_log) idx with
                       | Some v => v
                       | None => REnv.(getenv) r idx
                       end
                end,
                Gamma)
        else None
      | Write prt idx val => fun Gamma =>
        let/opt3 action_log, val, Gamma_new := interp_action Gamma sched_log action_log val in
        if may_write sched_log action_log prt idx then
          Some (log_cons idx (LE LogWrite prt val) action_log, Bits.nil, Gamma_new)
        else None
      | Unop fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, (CircuitPrimSpecs.sigma1 fn) arg1, Gamma)
      | Binop fn arg1 arg2 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        let/opt3 action_log, arg2, Gamma := interp_action Gamma sched_log action_log arg2 in
        Some (action_log, (CircuitPrimSpecs.sigma2 fn) arg1 arg2, Gamma)
      | ExternalCall fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, sigma fn arg1, Gamma)
      | APos _ a => fun Gamma =>
        interp_action Gamma sched_log action_log a
      end Gamma.

    Definition interp_rule (sched_log: Log) (rl: rule) : option Log :=
      match interp_action CtxEmpty sched_log log_empty rl with
      | Some (l, _, _) => Some l
      | None => None
      end.
  End Action.

  Section Scheduler.
    Context (r: REnv.(env_t) (fun idx => bits (R idx))).
    Context (sigma: forall f, CSig_denote (Sigma f)).
    Context (rules: rule_name_t -> rule).

    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      let interp_try rl s1 s2 :=
          match interp_rule r sigma sched_log (rules rl) with
          | Some l => interp_scheduler' (log_app l sched_log) s1
          | None => interp_scheduler' sched_log s2
          end in
      match s with
      | Done => sched_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler' sched_log s
      end.

    Definition interp_scheduler (s: scheduler) :=
      interp_scheduler' log_empty s.
  End Scheduler.

  Definition interp_cycle (sigma: forall f, CSig_denote (Sigma f)) (rules: rule_name_t -> rule)
             (s: scheduler) (r: REnv.(env_t) (fun idx => bits (R idx))) :=
      commit_update r (interp_scheduler r sigma rules s).
End Interp.
