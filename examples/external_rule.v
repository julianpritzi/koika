(*! Calling external (verilog) modules from Kôika !*)
Require Import Koika.Frontend.
Require Import Koika.TypedParsing.
Require Koika.TypedStd.

(* Koika.Std.Fifo1 is a polymorphic one-element fifo.

  The type of the fifo is indexed by the type of the data it holds, here we
  specialize the type of the fifo to fifo that holds [bits_t 5] values. *)

Module FifoParams <: TypedStd.Fifo.
  Definition T := bits_t 5.
End FifoParams.

Module Bits5Fifo := TypedStd.Fifo1 FifoParams.

(* fromIO is the state of an instance of Bits5Fifo *)
Inductive reg_t :=
| fromIO (_: Bits5Fifo.reg_t)
| ioPin
| Rdata.

Definition R r :=
  match r with
  | fromIO f => Bits5Fifo.R f
  | ioPin => bits_t 5
  | Rdata => bits_t 5
  end.

Definition r idx : R idx :=
  match idx with
  | fromIO f => Bits5Fifo.r f
  | ioPin => Bits.zero
  | Rdata => Bits.zero
  end.

(* Rules *)

(* This [_outsideWorld] rule is going to be declared external.  No circuitry will be
   generated for it when compiling to Verilog; instead, it will be removed and
   inputs and outputs will be generated to delegate its work to an external
   circuit *)
Definition _outsideWorld : action R empty_Sigma :=
  <{
      let data := read0(ioPin) in
      fromIO.(Bits5Fifo.enq)(data)
  }>.

Check _outsideWorld.

Definition _receive : action R empty_Sigma :=
  <{
      let dequeued := fromIO.(Bits5Fifo.deq)() in
      if (dequeued == Ob~0~0~0~1~0) then
        write0(Rdata, Ob~0~0~0~0~1)
      else
        fail
  }>.

Inductive rule_name_t :=
  outsideWorld | receive.

Definition rules :=
           (fun rl => match rl with
                   | receive => _receive
                   | outsideWorld => _outsideWorld
                   end).

Definition bring : scheduler :=
  outsideWorld |> receive |> done.

(* Annotating [outsideWorld] in [koika_rule_external] below indicates that the
   corresponding rule should be removed by the Verilog backend to let us insert
   an external implementation instead. *)
Definition package : interop_package_t :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external r :=
                     match r with outsideWorld => true | _ => false end;
                   koika_scheduler := bring;
                   koika_module_name := "external_rule" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "external_rule.ml" prog.
