Here is the TODO list.

### Current
- Processor design related.
  - [ ] use BRAM for the registers R.
  - [ ] simplify the Jump related instructions, produce a signal (Jump:bool) and an address (if jump is T) in the EX stage, instead of doing in IF.
 
- HOL4 processor model.
  - [ ] use non-blocking assignment for most variables, because of the single module. 



### Long term
- [ ] optimize the compilation time (mainly generate the *tstate*), which now uses more than 500s.
