(*! Tools | Functions defined on typed ASTs !*)
Require Export Koika.Member Koika.TypedSyntax.
Require Import Koika.Primitives Koika.TypedSemantics.
Import PrimTyped.
From Coq Require BinaryString OctalString HexString HexadecimalString DecimalString.
Require Import Ascii.

Require Import Magic.

(* Require Import Koika.Hoare. *)
Section TypedSyntaxMacros.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Notation action := (action pos_t var_t fn_name_t).
  Notation InternalFunction R Sigma sig tau := (InternalFunction pos_t var_t fn_name_t R Sigma sig tau).

  (* Section Switching.
    Notation action := (action R Sigma).

    Fixpoint muxtree {sig tau} {sz} (bit_idx : nat) (k: var_t) {m : member (k, bits_t sz) sig} {bsz} (bodies: bits bsz -> action sig tau) :=
      match bsz return (bits bsz -> action sig tau) -> action sig tau with
      | 0 => fun bodies => bodies Ob
      | S n => fun bodies =>
        (* FIXME add a version of sel taking a compile-time constant? *)
        If (Binop (Bits2 (Sel _)) (Var m) (Const (value_of_bits (Bits.of_nat _ bit_idx))))
          (muxtree (S bit_idx) k (fun bs => bodies bs~1))
          (muxtree (S bit_idx) k (fun bs => bodies bs~0))
      end bodies.

    Definition CompleteMuxTree {sig tau} {sz} (k: var_t) {m : member (k, bits_t sz) sig} (branches: bits sz -> action sig tau) :=
      muxtree 0 k branches.


    Inductive switch_style :=
      | TreeSwitch.
      (* | OrTreeSwitch (nbits: nat)
      | NestedSwitch
      | SequentialSwitchTt
      | SequentialSwitch (tau: type) (output_var: var_t). *)

    Definition CompleteSwitch {sig tau} (style: switch_style)
      {sz} (k: var_t) {m : member (k, bits_t sz) sig}
      (branch_bodies: index (pow2 sz) -> action sig tau) :=
      (* let branches bodies := gen_branches sz (pow2 sz) bodies in *)
      match style with
      | TreeSwitch =>
        CompleteMuxTree k (fun bs => branch_bodies (Bits.to_index_safe bs))
      (* | OrTreeSwitch nbits =>
        UCompleteOrTree sz nbits var (fun bs => branch_bodies (Bits.to_index_safe bs))
      | NestedSwitch =>
        uswitch_nodefault (UVar var) (branches branch_bodies)
      | SequentialSwitchTt =>
        uswitch_stateful (UVar var) (branches branch_bodies)
      | SequentialSwitch output_type output_var =>
        let branch_bodies idx := UAssign output_var (branch_bodies idx) in
        UBind output_var
              (uinit output_type)
              (USeq (uswitch_stateful (UVar var) (branches branch_bodies))
                    (UVar output_var)) *)
      end.
    End Switching. *)

  (* filter a single char out of a string *)
  Local Fixpoint filters' (s : string) (a : ascii) : string :=
    match s with
    | EmptyString => EmptyString
    | String c s' => if ascii_dec c a
      then filters' s' a
      else String c (filters' s' a)
    end.
  (* filter a set of chars out of a string *)
  Fixpoint filter_string (s : string) (l : list ascii) : string :=
    match l with
    | a :: l' => filter_string (filters' s a) l'
    | [] => s
    end.
  (* Coq's implementation just silently returns 0 on an invalid string -
    for better error recognition these methods are redefined here returning option *)
  Local Fixpoint num_string_to_option_N' (s : string) (base : N) (convert : Ascii.ascii -> option N) (remainder : option N) : option N :=
    match s with
    | EmptyString => remainder
    | String c s' => num_string_to_option_N' s' base convert
      (match remainder, convert c with
      | Some rem, Some c_v => Some (N.add (N.mul base rem) c_v)
      | _, _ => None
      end)
    end.
  Local Definition num_string_to_option_N (s : string) (base : N) (convert : Ascii.ascii -> option N) : option N :=
    match s with
    | EmptyString => None
    | String _ _ => num_string_to_option_N' s base convert (Some 0%N)
    end.

  Definition bin_string_to_N s := (must (num_string_to_option_N s 2 BinaryString.ascii_to_digit)).
  Definition oct_string_to_N s := (must (num_string_to_option_N s 8 OctalString.ascii_to_digit)).
  Definition dec_string_to_N s := (must (option_map N.of_uint (DecimalString.NilZero.uint_of_string s))).
  Definition hex_string_to_N s := (must (num_string_to_option_N s 16 HexString.ascii_to_digit)).

  (* Section Simple.
    Notation action := (action R Sigma).

    Fixpoint switch {vk vtau} {sig tau} (m: member (vk, vtau) sig)
             (default: action sig tau)
             (branches: list (action sig vtau * action sig tau)) : action sig tau :=
      match branches with
      | nil => default
      | (label, action) :: branches =>
        If (Binop (Eq _ false) (Var m) label)
           action (switch m default branches)
      end.

    Definition switch_pure {vk vtau} {sig tau} (m: member (vk, vtau) sig)
               (default: action sig tau)
               (branches: list (vtau * action sig tau)) : action sig tau :=
      switch m default (List.map (fun p => (Const (tau := vtau) (fst p), snd p)) branches).
  End Simple. *)

  Section Lift.
    Context {reg_t' ext_fn_t': Type}.

    Context {R': reg_t' -> type}.
    Context {Sigma': ext_fn_t' -> ExternalSignature}.

    Class Intfun_lift {A A' B} (fA: A -> B) (fA': A' -> B) := {
      lift_fn: A' -> A;
      lift_comm: (* forall a' : A', *) fA' (* a' *) = (fun a' => fA (lift_fn a'));
    }.

    Context (lR: Intfun_lift R R')
            (lSigma: Intfun_lift Sigma Sigma').

    Section lift_intfun.
      Context {tau: type}.
      Context {argspec : tsig var_t}.
      Context (lift: forall (a: action R' Sigma' argspec tau),
                  action R Sigma argspec tau).

      (*
       * Assume you have a function in a Modul:
       * ```
       * Inductive reg_t := reg1.
       * Definition R (r : reg_t) := bits_t 2.
       * Definition func : function R empty_Sigma := <{
       *   fun f () : bits_t 2 =>
       *     read0(reg1)
       * }>.
       * ```
       *
       * This function is typed using the [R] and [Sigma]
       * of the modul. However, to call this function in
       * a composition of modules it needs to be typed with
       * the [super_R] and (possibly) [super_Sigma] of this
       * larger module. (See TypedSyntax.v [InternalCall] -
       * `body` has the same R/Sigma as the retuned type)
       *
       * This function will lift a given action [act]
       *)
      (* Definition lift_intfun'
                  (fn : InternalFunction R' Sigma' argspec tau) :
          InternalFunction R Sigma argspec tau :=
          {| int_name := fn.(int_name);
            int_body := lift fn.(int_body) |}. *)

    End lift_intfun.

    Fixpoint lift
             {sig tau}
             (a: action R' Sigma' sig tau)
      : action R Sigma sig tau :=
      match a with
      | Fail tau => Fail tau
      | Var vr => Var vr
      | Const cst => Const cst
      | Assign vr ex => Assign vr (lift ex)
      | Seq a1 a2 => Seq (lift a1) (lift a2)
      | Bind var ex body => Bind var (lift ex) (lift body)
      | If cond tbranch fbranch => If (lift cond) (lift tbranch) (lift fbranch)
      | Read port idx => rew <- [fun e => _ (e idx)] lR.(lift_comm) (* idx *) in
        Read port (lR.(lift_fn) idx)
      | Write port idx value =>
        Write port (lR.(lift_fn) idx) (lift (rew [fun e => _ (e idx)] lR.(lift_comm) (* idx *) in value))
      | Unop fn arg1 => Unop fn (lift arg1)
      | Binop fn arg1 arg2 => Binop fn (lift arg1) (lift arg2)
      | ExternalCall fn arg =>
        rew <- [fun e => _ (retSig (e fn))] lSigma.(lift_comm) (* fn *) in
        ExternalCall (lift_fn fn)
          (rew [fun e => _ (arg1Sig (e fn))] lSigma.(lift_comm) (* fn *) in lift arg)
      | InternalCall fn args =>
        InternalCall {| int_name := fn.(int_name); int_body := lift fn.(int_body) |}
          (cmapv (fun _ => lift) args)
      | APos pos a => APos pos (lift a)
      end.

    Context {REnv: Env reg_t}.
    Context {REnv': Env reg_t'}.

    (* Definition unlift_REnv
               (f: type -> Type)
               (env: REnv.(env_t) (fun x => f (R x)))
    : REnv'.(env_t) (fun x => f (R' x)).
      set (idk := REnv'.(create) (fun reg: reg_t' => REnv.(getenv) env (lR.(lift_fn) reg))).
      simpl in idk.H
      rewrite <- lR.(lift_comm) in idk.
      (* rew lR.(lift_comm) _ in *)rew lR.(lift_comm) _ in
        REnv'.(create) (fun reg: reg_t' => REnv.(getenv) env (lR.(lift_fn) reg)).

    Definition unlift_sigma
               (sigma: forall f, Sig_denote (Sigma f))
      : forall f, Sig_denote (Sigma' f) :=
      rew <- [fun Sigma' => forall f, Sig_denote (Sigma' f)] lSigma.(lift_ok).(lift_comm) in
        (fun f => sigma (lSigma.(lift_fn) f)).

    Definition lift_REnv
               (f: type -> Type)
               (env: REnv.(env_t) (fun x => f (R x)))
               (env': REnv'.(env_t) (fun x => f (R' x)))
      : REnv.(env_t) (fun x => f (R x)) :=
      Environments.fold_right
        REnv'
        (fun k v acc =>
           (REnv.(putenv))
             acc (lR.(lift_fn) k)
             (rew [fun R' => f (R' k)] lR.(lift_ok).(lift_comm) in v))
        env' env.

    Context (r: REnv.(env_t) R).
    Context (sigma: forall f, Sig_denote (Sigma f)). *)

    (* Lemma lift_unlift_REnv (f: type -> Type):
      forall l, lift_REnv f l (unlift_REnv f l) = l.
    Proof.
      unfold lift_REnv, unlift_REnv, Environments.fold_right.
      induction finite_elements; cbn.
      - reflexivity.
      - intros.
        rewrite IHl. apply put_get_eq.
        unfold eq_rect_r.
        rewrite getenv_rew'.
        rewrite getenv_create.
        rewrite rew_compose.
        apply __magic__.
    Qed. *)

    (* Lemma unlift_lift_REnv (f: type -> Type):
      forall ev ev0, unlift_REnv f (lift_REnv f ev0 ev) = ev.
    Proof.
      unfold lift_REnv, unlift_REnv, Environments.fold_right.
      intros.
      apply equiv_eq; intros k.
      unfold eq_rect_r; rewrite getenv_rew', getenv_create.
      (* LR k is in the list, so must be hit, and by injectivity it's not replaced *)
        apply __magic__.
    Qed. *)

    (* Lemma getenv_unlift_REnv (f: type -> Type) :
      forall ev k,
        REnv'.(getenv) (unlift_REnv f ev) k =
        rew <- [fun R' => f (R' k)] lR.(lift_ok).(lift_comm) in
          REnv.(getenv) ev (lift_fn lR k).
    Proof.
      unfold unlift_REnv; intros.
      unfold eq_rect_r.
      rewrite getenv_rew'.
      rewrite getenv_create; reflexivity.
    Qed. *)

    (* Lemma getenv_lift_REnv_lifted (f: type -> Type) :
      forall ev ev0 k',
        REnv.(getenv) (lift_REnv f ev0 ev) (lift_fn lR k') =
        rew [fun R' => f (R' k')] lR.(lift_ok).(lift_comm) in
          REnv'.(getenv) ev k'.
    Proof.
      apply __magic__.
    Qed. *)

    (* Lemma getenv_lift_REnv_unlifted (f: type -> Type) :
      forall ev ev0 k,
        (forall k', lift_fn lR k' <> k) ->
        REnv.(getenv) (lift_REnv f ev0 ev) k =
        REnv.(getenv) ev0 k.
    Proof.
      apply __magic__.
    Qed. *)
  End Lift.
End TypedSyntaxMacros.

Instance LiftId {A B} {fn : A -> B} : @Intfun_lift A A B fn fn := {|
  lift_fn := id;
  lift_comm := eq_refl;
|}.
(* Notation lift_intfun lR lSigma fn :=
  (lift_intfun' (lift lR lSigma) fn). *)

(* Require Import CompactLogs. *)

(* Arguments unlift_sigma {ext_fn_t} {Sigma} {ext_fn_t'} {Sigma'} {lSigma} sigma f _: assert. *)

(* Notation unlift_Log := (unlift_REnv _ LogEntry). *)
(* Notation unlift_r := (unlift_REnv _ type_denote). *)

(* Notation lift_Log := (lift_REnv _ LogEntry). *)
(* Notation lift_r := (lift_REnv _ type_denote). *)
