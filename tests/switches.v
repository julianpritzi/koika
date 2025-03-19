(*! Test various forms of switches !*)
Require Import Koika.Frontend.
Require Import Koika.Parsing.

Definition clocksz := 2.
Definition idxsz := 5.
Definition datasz := 64.

Inductive reg_t := clock | index | data (idx: Vect.index (pow2 idxsz)) | output.
Inductive rule_name_t := sequential_copy | tree_copy | comb_copy | function_switch | manual_switch | tick.

Definition R r :=
  match r with
  | clock => bits_t 2
  | index => bits_t idxsz
  | data _ => bits_t datasz
  | output => bits_t datasz
  end.

Definition r idx : R idx :=
  match idx with
  | clock => Bits.zero
  | index => Bits.zero
  | data idx => Bits.app (Bits.zeroes (datasz - idxsz)) (Bits.of_index idxsz idx)
  | output => Bits.zero
  end.

Definition rule clock_condition style : uaction reg_t empty_ext_fn_t :=
  {{
      if read0(clock) != `clock_condition` then fail else pass;
      let idx := read0(index) in
      write0(output, `UCompleteSwitch style idxsz "idx" (fun idx => {{ read0(data idx) }})`)
  }}.

Definition another_fn : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun another_fn (x: bits_t 1) : bits_t 1 => x }}.

(* Regression test *)
Definition simple_match_fn : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun simple_match_fn (x: bits_t 1) : bits_t 1 =>
       match x with
       | #Ob~0 =>
           if (another_fn(Ob~0))
           then Ob~0
           else Ob~1
       | #Ob~1 =>
           Ob~1
       return default: (Ob~0)
       end
   }}.


Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | sequential_copy => rule {{ |clocksz`d0| }} (SequentialSwitch (bits_t datasz) "tmp")
  | tree_copy => rule {{ |clocksz`d1| }} TreeSwitch
  | comb_copy => rule {{ |clocksz`d2| }} NestedSwitch
  | function_switch => {{ ignore(simple_match_fn (Ob~0)) }}
  | manual_switch => {{ match read0(clock) with
                       | #Ob~0~0 => pass
                       | #Ob~0~1 => pass
                       | #Ob~1~0 => pass
                       | #Ob~1~1 => pass
                       return default: pass
                       end }}
  | tick => {{ write0(clock, read0(clock) + |clocksz`d1|);
              let idx := read0(index) in
              write0(index, idx << |idxsz`d2| + idx + |idxsz`d17|) }}
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  sequential_copy |> tree_copy |> comb_copy |> manual_switch |> function_switch |> tick |> done.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external _ := false;
                   koika_scheduler := sched;
                   koika_module_name := "switches" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "switches.ml" prog.
