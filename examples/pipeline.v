(*! Building simple pipelines !*)
Require Import Koika.Frontend.
Require Import Koika.TypedParsing.

Inductive reg_t := r0 | outputReg | inputReg | invalid | correct.
Inductive ext_fn_t := Stream | F | G.
Inductive rule_name_t := doF | doG.

Definition sz := (pow2 5).

Definition R r :=
  match r with
  | r0 => bits_t sz
  | inputReg => bits_t sz
  | outputReg => bits_t sz
  | invalid | correct => bits_t 1
  end.

Definition r reg : R reg :=
  match reg with
  | r0 => Bits.zero
  | outputReg => Bits.zero
  | inputReg => Bits.zero
  | invalid => Ob~1
  | correct => Ob~1
  end.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | Stream => {$ bits_t sz ~> bits_t sz $}
  | F => {$ bits_t sz ~> bits_t sz $}
  | G => {$ bits_t sz ~> bits_t sz $}
  end.

Definition _doF : action R Sigma := <{
  let v := read0(inputReg) in
  write0(inputReg, extcall Stream(v));
  let invalid := read1(invalid) in
  if invalid then (
    write1(invalid, Ob~0);
    write0(r0,extcall F(v))
  ) else fail
}>.

Definition _doG : action R Sigma := <{
  let invalid := read0(invalid) in
  if !invalid then
    let data := read0(r0) in
    let v := read0(outputReg) in
    write0(outputReg, extcall Stream(v));
    write0(invalid, Ob~1);
    if extcall G(data) == extcall G(extcall F(v)) then
      pass
    else
      write0(correct, Ob~0)
  else
    fail
}>.

Definition rules :=
  (* tc_rules R Sigma *)
           (fun rl => match rl with
                   | doF => _doF
                   | doG => _doG
                   end).

Definition pipeline : scheduler :=
  doG |> doF |> done.

Definition external (r: rule_name_t) := false.

Definition circuits :=
  compile_scheduler rules external pipeline.

Definition circuits_result sigma :=
  interp_circuits sigma circuits (lower_r (ContextEnv.(create) r)).

Definition cpp_extfuns := "class extfuns {
public:
  static bits<32> stream(bits<32> lfsr) {
    return lfsr + bits<32>{1};
  }

  static bits<32> f(bits<32> x) {
    return ~(x << bits<32>{2}) - bits<32>{1};
  }

  static bits<32> g(bits<32> x) {
    return bits<32>{5} + ((x + bits<32>{1}) >> bits<32>{1});
  }
};".

Definition ext_fn_names fn :=
  match fn with
  | Stream => "stream"
  | F => "f"
  | G => "g"
  end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r reg;
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := pipeline;
                   koika_module_name := "pipeline" |};

     ip_sim := {| sp_ext_fn_specs fn :=
                   {| efs_name := ext_fn_names fn;
                      efs_method := false |};
                 sp_prelude := Some cpp_extfuns |};

     ip_verilog := {| vp_ext_fn_specs fn :=
                       {| efr_name := ext_fn_names fn;
                          efr_internal := true |} |} |}.

Definition prog := Interop.Backends.register package.
Extraction "pipeline.ml" prog.
