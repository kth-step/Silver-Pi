Here is the TODO list.

### Current
- Processor design related.
  - [ ] use BRAM for the registers R.
  - [ ] simplify the Jump related instructions, produce a signal (Jump:bool) and an address (if jump is T) in the EX stage, instead of doing in IF.
 
- HOL4 processor model.
  - [ ] use non-blocking assignment for most variables, because of the single module. 

### Long term
- [ ] optimize the compilation time (mainly generate the *tstate*), which now uses more than 500s.
- [ ] checker for writes to make sure e.g. not multiple processes write to the same variable (Andreas will deal with this eventually)

### Nice-to-haves for the translator
- [ ] Better handling on unpacked vs. packed arrays
- [ ] Support for record update syntax. Easiest to handle by pre-processing rather than inside the translator.
- [ ] Support for process-local variables
