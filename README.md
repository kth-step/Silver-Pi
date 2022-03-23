# hw-verification-silver
Pipelined Silver processor: implementation in Verilog and verification in HOL4.

### Folder
- `model`: pipelined Silver processor model in HOL4, based on the verified Verilog semantics and translator.
- `verilog_src`: Verilog source code for the processor.
- `silver_isa`: Silver ISA specification in L3.
- `tests`: test programs generated by cakeml.

### Building
Reqirements:

[HOL4](https://github.com/HOL-Theorem-Prover/HOL)

[verified (System) Verilog](https://github.com/CakeML/hardware/tree/v3)

### Reference
[Source code of the verified single-cycle Silver processor](https://github.com/CakeML/hardware/tree/dc281059bd3a19e478fb211aadda1c2ac7891fa9)

Paper: [Verified compilation on a verified processor](https://doi.org/10.1145/3314221.3314622)
