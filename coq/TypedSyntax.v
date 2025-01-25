(*! Language | Typed ASTs !*)
Require Export Koika.Common Koika.Environments Koika.Types Koika.Primitives.

Import PrimTyped PrimSignatures.

Section Syntax.
  Context {pos_t var_t rule_name_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  (*
    tau: the type that an expression evaluates to
      e.g. `Const (Bits.of_nat 5 18)` then tau is `bits_t 5`
    var_t: the type of identifiers - as far as I know always [string]
      e.g. in `let a := ... in ...` a is parsed (and stored in the AST) as string

    *)
  Inductive action : tsig var_t -> type -> Type :=
  | Fail {sig} tau : action sig tau
  | Var {sig} {k: var_t} {tau: type}
        (m: member (k, tau) sig) : action sig tau
  | Const {sig} {tau: type}
          (cst: type_denote tau) : action sig tau
  | Assign {sig} {k: var_t} {tau: type}
           (m: member (k, tau) sig) (ex: action sig tau) : action sig unit_t
  | Seq {sig tau}
        (r1: action sig unit_t)
        (r2: action sig tau) : action sig tau
  | Bind {sig} {tau tau'}
         (var: var_t)
         (ex: action sig tau)
         (body: action (List.cons (var, tau) sig) tau') : action sig tau'
  | If {sig tau}
       (cond: action sig (bits_t 1))
       (tbranch fbranch: action sig tau) : action sig tau
  | Read {sig}
         (port: Port)
         (idx: reg_t): action sig (R idx)
  | Write {sig}
          (port: Port) (idx: reg_t)
          (value: action sig (R idx)) : action sig unit_t
  | Unop {sig}
          (fn: fn1)
          (arg1: action sig (arg1Sig (Sigma1 fn)))
    : action sig (retSig (Sigma1 fn))
  | Binop {sig}
          (fn: fn2)
          (arg1: action sig (arg1Sig (Sigma2 fn)))
          (arg2: action sig (arg2Sig (Sigma2 fn)))
    : action sig (retSig (Sigma2 fn))
  | ExternalCall {sig}
                 (fn: ext_fn_t)
                 (arg: action sig (arg1Sig (Sigma fn)))
    : action sig (retSig (Sigma fn))
  | InternalCall {sig tau}
                 (* TODO -- why does argspec need to be reversed?? *)
                 {argspec : tsig var_t}
                 (fn : InternalFunction' fn_name_t (action argspec tau))
                 (args: context (fun k_tau => action sig (snd k_tau)) argspec)
    : action sig tau
  | APos {sig tau} (pos: pos_t) (a: action sig tau)
    : action sig tau.

  Fixpoint ctx_Forall {K} {V: K -> Type} (P: forall (k: K), V k -> Prop) {sig} (ctx: context V sig) :=
    match ctx with
    | CtxEmpty => True
    | CtxCons k v ctx => P k v /\ ctx_Forall P ctx
    end.

  Definition acontext (sig argspec: tsig var_t) :=
    context (fun k_tau => action sig (snd k_tau)) argspec.

  (* This induction principle contains all necessary
    hypothesis to do an actual induction over an `action`
    without resorting to manual Fixpoint proofs.

    Note that this principle can only be used on goals
    of the form `Pa /\ Pargs` where `Pa` stand for an arbitrary
    proposition over actions while `Pargs` represents an
    analogus porp extended to contexts of actions (just
      like they are used by `InternalCall`)

    As an example, have a look at the proofs in Hoare.v
  *)
  Lemma action_ind_complete :
    (* Propositions *)
    forall P : forall {sig tau}, action sig tau -> Prop,
    forall P' : forall {sig argspec}, acontext sig argspec -> Prop,

    (* All cases for the normal action *)
    (forall (sig : tsig var_t) (tau : type),
      @P sig tau (Fail tau)) ->
    (forall (sig : list (var_t * type)) (k : var_t) (tau : type) (m : member (k, tau) sig),
      @P sig tau (Var m)) ->
    (forall (sig : tsig var_t) (tau : type) (cst : tau),
      @P sig tau (Const cst)) ->
    (forall (sig : list (var_t * type)) (k : var_t) (tau : type) (m : member (k, tau) sig) (ex : action sig tau),
      @P sig tau ex ->
      @P sig unit_t (Assign m ex)) ->
    (forall (sig : tsig var_t) (tau : type) (r1 : action sig unit_t) (r2 : action sig tau),
      @P sig unit_t r1 ->
      @P sig tau r2 ->
      @P sig tau (Seq r1 r2)) ->
    (forall (sig : tsig var_t) (tau tau' : type) (var : var_t) (ex : action sig tau) (body : action ((var, tau) :: sig) tau'),
      @P sig tau ex ->
      @P ((var, tau) :: sig) tau' body ->
      @P sig tau' (Bind var ex body)) ->
    (forall (sig : tsig var_t) (tau : type) (cond : action sig (bits_t 1)) (tbranch : action sig tau) (fbranch : action sig tau),
      @P sig (bits_t 1) cond ->
      @P sig tau tbranch ->
      @P sig tau fbranch ->
      @P sig tau (If cond tbranch fbranch)) ->
    (forall (sig : tsig var_t) (port : Port) (idx : reg_t),
      @P sig (R idx) (Read port idx)) ->
    (forall (sig : tsig var_t) (port : Port) (idx : reg_t) (value : action sig (R idx)),
      @P sig (R idx) value ->
      @P sig unit_t (Write port idx value)) ->
    (forall (sig : tsig var_t) (fn : fn1) (arg1 : action sig (arg1Sig (Sigma1 fn))),
      @P sig (arg1Sig (Sigma1 fn)) arg1 ->
      @P sig (retSig (Sigma1 fn)) (Unop fn arg1)) ->
    (forall (sig : tsig var_t) (fn : fn2) (arg1 : action sig (arg1Sig (Sigma2 fn))) (arg2 : action sig (arg2Sig (Sigma2 fn))),
      @P sig (arg1Sig (Sigma2 fn)) arg1 ->
      @P sig (arg2Sig (Sigma2 fn)) arg2 ->
      @P sig (retSig (Sigma2 fn)) (Binop fn arg1 arg2)) ->
    (forall (sig : tsig var_t) (fn : ext_fn_t) (arg : action sig (arg1Sig (Sigma fn))),
      @P sig (arg1Sig (Sigma fn)) arg ->
      @P sig (retSig (Sigma fn)) (ExternalCall fn arg)) ->
    (forall (sig : tsig var_t) (tau : type) (argspec : tsig var_t) (fn : InternalFunction' fn_name_t (action argspec tau)) (args : context (fun k_tau : var_t * type => action sig (snd k_tau)) argspec),
      @P argspec tau fn.(int_body) ->
      @P' sig argspec args ->
      @P sig tau (InternalCall fn args)) ->
    (forall (sig : tsig var_t) (tau : type) (pos : pos_t) (a : action sig tau),
      @P sig tau a ->
      @P sig tau (APos pos a)) ->

    (* All cases for action contexts *)
    (forall sig,
      @P' sig [] CtxEmpty) ->
    (forall sig n tau argspec a args,
      @P sig tau a ->
      @P' sig argspec args ->
      @P' sig ((n,tau) :: argspec) (CtxCons (n,tau) a args)) ->

    (* goal *)
    (forall {sig tau} (a : action sig tau),
    @P sig tau a) /\
    (forall {sig argspec} (args : acontext sig argspec),
    @P' sig argspec args).
  Proof.
    intros P P' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H1' H2'.
    assert (Hargs : (forall (sig : tsig var_t) (tau : type) (a : action sig tau), P sig tau a) -> forall (sig argspec : tsig var_t) (args : acontext sig argspec), P' sig argspec args).
    + intro Ha. fix IH 3.
      destruct args.
      * apply H1'.
      * destruct k.
        apply H2'.
        - apply Ha.
        - apply IH.
    + assert (Ha : forall (sig : tsig var_t) (tau : type) (a : action sig tau), P sig tau a).
      * fix IH 3.
        destruct a.
        - apply H1.
        - apply H2.
        - apply H3.
        - apply H4; apply IH.
        - apply H5; apply IH.
        - apply H6; apply IH.
        - apply H7; apply IH.
        - apply H8.
        - apply H9. apply IH.
        - apply H10. apply IH.
        - apply H11; apply IH.
        - apply H12. apply IH.
        - apply H13. apply IH.
          apply (Hargs IH).
        - apply H14. apply IH.
      * split.
        - apply (Ha).
        - apply (Hargs Ha).
  Qed.

  Definition add (n1 n2 : nat) : nat.
    induction n1.
    - exact n2.
    - exact (S IHn1).
  Defined.

  (* Print add. *)


  Goal forall n1 n2, add n1 n2 = Nat.add n1 n2.
    induction n1.
    reflexivity.
    intros.
    simpl (S n1 + _).
    rewrite <- IHn1.
    reflexivity.
  Qed.

  Definition action_rect_complete
    (* Propositions *)
    (P : forall {sig tau}, action sig tau -> Type)
    (P' : forall {sig argspec}, acontext sig argspec -> Type)

    (* All cases for the normal action *)
    (f_fail : forall sig tau,
      @P sig tau (Fail tau))
    (f_var : forall sig k tau (m : member (k, tau) sig),
      @P sig tau (Var m))
    (f_const : forall sig tau cst,
      @P sig tau (Const cst))
    (f_assign : forall sig k tau (m : member (k, tau) sig) (ex : action sig tau),
      @P sig tau ex ->
      @P sig unit_t (Assign m ex))
    (f_seq : forall sig tau (r1 : action sig unit_t) (r2 : action sig tau),
      @P sig unit_t r1 ->
      @P sig tau r2 ->
      @P sig tau (Seq r1 r2))
    (f_bind : forall sig (tau tau' : type) (var : var_t) (ex : action sig tau) (body : action ((var, tau) :: sig) tau'),
      @P sig tau ex ->
      @P ((var, tau) :: sig) tau' body ->
      @P sig tau' (Bind var ex body))
    (f_if : forall sig tau (cond : action sig (bits_t 1)) (tbranch : action sig tau) (fbranch : action sig tau),
      @P sig (bits_t 1) cond ->
      @P sig tau tbranch ->
      @P sig tau fbranch ->
      @P sig tau (If cond tbranch fbranch))
    (f_read : forall sig (port : Port) (idx : reg_t),
      @P sig (R idx) (Read port idx))
    (f_write : forall sig (port : Port) (idx : reg_t) (value : action sig (R idx)),
      @P sig (R idx) value ->
      @P sig unit_t (Write port idx value))
    (f_unop : forall sig (fn : fn1) (arg1 : action sig (arg1Sig (Sigma1 fn))),
      @P sig (arg1Sig (Sigma1 fn)) arg1 ->
      @P sig (retSig (Sigma1 fn)) (Unop fn arg1))
    (f_binop : forall sig (fn : fn2) (arg1 : action sig (arg1Sig (Sigma2 fn))) (arg2 : action sig (arg2Sig (Sigma2 fn))),
      @P sig (arg1Sig (Sigma2 fn)) arg1 ->
      @P sig (arg2Sig (Sigma2 fn)) arg2 ->
      @P sig (retSig (Sigma2 fn)) (Binop fn arg1 arg2))
    (f_ext_call : forall sig (fn : ext_fn_t) (arg : action sig (arg1Sig (Sigma fn))),
      @P sig (arg1Sig (Sigma fn)) arg ->
      @P sig (retSig (Sigma fn)) (ExternalCall fn arg))
    (f_int_call : forall sig (tau : type) (argspec : tsig var_t) (fn : InternalFunction' fn_name_t (action argspec tau)) (args : context (fun k_tau : var_t * type => action sig (snd k_tau)) argspec),
      @P argspec tau fn.(int_body) ->
      @P' sig argspec args ->
      @P sig tau (InternalCall fn args))
    (f_apos : forall sig (tau : type) (pos : pos_t) (a : action sig tau),
      @P sig tau a ->
      @P sig tau (APos pos a))

    (* All cases for action contexts *)
    (f_args_emtyp : forall sig,
      @P' sig [] CtxEmpty)
    (f_args_cons : forall sig n tau argspec a args,
      @P sig tau a ->
      @P' sig argspec args ->
      @P' sig ((n,tau) :: argspec) (CtxCons (n,tau) a args))

    : (* goal *)
    (forall {sig tau} (a : action sig tau),
    @P sig tau a) *
    (forall {sig argspec} (args : acontext sig argspec),
    @P' sig argspec args).
  Proof.
    (* intros P P' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H1' H2'. *)
    assert (Hargs : (forall (sig : tsig var_t) (tau : type) (a : action sig tau), P sig tau a) -> forall (sig argspec : tsig var_t) (args : acontext sig argspec), P' sig argspec args).
    + intro Ha. fix IH 3.
      destruct args.
      * apply f_args_emtyp.
      * destruct k.
        apply f_args_cons.
        - apply Ha.
        - apply IH.
    + assert (Ha : forall (sig : tsig var_t) (tau : type) (a : action sig tau), P sig tau a).
      * fix IH 3.
        destruct a.
        - apply f_fail.
        - apply f_var.
        - apply f_const.
        - apply f_assign; apply IH.
        - apply f_seq; apply IH.
        - apply f_bind; apply IH.
        - apply f_if; apply IH.
        - apply f_read.
        - apply f_write. apply IH.
        - apply f_unop. apply IH.
        - apply f_binop; apply IH.
        - apply f_ext_call. apply IH.
        - apply f_int_call. apply IH.
          apply (Hargs IH).
        - apply f_apos. apply IH.
      * split.
        - apply (Ha).
        - apply (Hargs Ha).
  Defined.

  Definition action_rec_complete
    (P : forall sig tau, action sig tau -> Set)
    (P' : forall sig argspec, acontext sig argspec -> Set) :=
    action_rect_complete P P'.

  (* Print action_rect_complete. *)

  Definition rule := action nil unit_t.
End Syntax.

Arguments action pos_t var_t fn_name_t {reg_t ext_fn_t} R Sigma sig tau : assert.
Arguments rule pos_t var_t fn_name_t {reg_t ext_fn_t} R Sigma : assert.

Notation InternalFunction pos_t var_t fn_name_t R Sigma sig tau :=
  (InternalFunction' fn_name_t (action pos_t var_t fn_name_t R Sigma sig tau)).
