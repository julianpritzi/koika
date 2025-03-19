(*! Implementation of a scoreboard !*)
Require Import Coq.Lists.List.

Require Import Koika.Frontend.
Require Import Koika.Parsing.
Require Import Koika.Std.

Module Type Scoreboard_sig.
  Parameter idx_sz:nat.
  Parameter maxScore:nat. (* Usually  maxScore ~= 3/4 *)
End Scoreboard_sig.

(* Definition read_style tau := SequentialSwitch tau "tmp". *)
Definition write_style := @SequentialSwitchTt var_t.
Definition read_style (nbits: nat) := @OrTreeSwitch var_t nbits.

Module Scoreboard (s:Scoreboard_sig).
  Definition sz:= s.idx_sz.
  Definition logScore := log2 s.maxScore.

  Module RfParams <: RfPow2_sig.
    Definition idx_sz := sz.
    Definition T := bits_t logScore.
    Definition init := Bits.zeroes logScore.
    Definition read_style := read_style logScore.
    Definition write_style := write_style.
  End RfParams.
  Module Rf := RfPow2 RfParams.

  Inductive reg_t := Scores (state: Rf.reg_t).
  Definition R r :=
    match r with
    | Scores n => Rf.R n
    end.

  Definition r idx : R idx :=
    match idx with
    | Scores n => Rf.r n
    end.

  Definition name_reg r :=
    match r with
    | Scores n => String.append "rf" (Rf.name_reg n)
    end.
  (* Internal functions *)
  Definition sat_incr : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun sat_incr (a: bits_t logScore) : bits_t logScore =>
          (* if ( a == #(Bits.of_nat logScore s.maxScore)) then fail(logScore) *)
          (* else *) a + #(Bits.of_nat logScore 1)
    }}.

  Definition sat_decr : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun sat_decr (a: bits_t logScore) : bits_t logScore =>
          (* if (a == |logScore`d0|) then fail(logScore) *)
          (* else *) (a - |logScore`d1|)
    }}.

  (* Interface: *)
  Definition insert : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun insert (idx: bits_t sz) : bits_t 0 =>
          let old_score := Scores.(Rf.read_1)(idx) in
          let new_score := sat_incr(old_score) in
          Scores.(Rf.write_1)(idx, new_score)
    }}.

  Definition remove : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun remove (idx: bits_t sz) : bits_t 0 =>
          let old_score := Scores.(Rf.read_0)(idx) in
          let new_score := sat_decr(old_score) in
          Scores.(Rf.write_0)(idx, new_score)
    }}.

  Definition search : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun search (idx: bits_t sz) : bits_t logScore =>
          Scores.(Rf.read_1)(idx)
    }}.
End Scoreboard.
