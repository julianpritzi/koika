(*! Using black-box Verilog models (combining Cuttlesim and Verilator) !*)
Require Import Koika.Frontend.
Require Import Koika.TypedParsing.

Module CoSimulation.
  Inductive reg_t := counter | blackbox_response.
  Inductive rule_name_t := increment_counter | call_blackbox.
  Inductive ext_fn_t := blackbox.

  Definition R r :=
    match r with
    | counter => bits_t 32
    | blackbox_response => bits_t 32
    end.

  Definition r idx : R idx :=
    match idx with
    | counter => Bits.zero
    | blackbox_response => Bits.zero
    end.

  Definition Sigma fn :=
    match fn with
    | blackbox => {$ bits_t 32 ~> bits_t 32 $}
    end.

  Definition _increment_counter : action R Sigma :=
    <{ write0(counter, read0(counter) + |32`d1|) }>.

  Definition _call_blackbox : action R Sigma :=
    <{ write0(blackbox_response, extcall blackbox(read0(counter))) }>.

  Definition cosimulation : scheduler :=
    call_blackbox |> increment_counter |> done.

  Definition rules :=
             (fun r => match r with
                    | increment_counter => _increment_counter
                    | call_blackbox => _call_blackbox
                    end).

  Definition external (_: rule_name_t) := false.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := cosimulation;
                     koika_module_name := "cosimulation" |};

       ip_sim := {| sp_ext_fn_specs _ := {| efs_name := "blackbox";
                                          efs_method := false |};
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs _ := {| efr_name := "blackbox";
                                              efr_internal := true |} |} |}.
End CoSimulation.

Definition prog := Interop.Backends.register CoSimulation.package.
