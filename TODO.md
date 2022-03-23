Here is the TODO list.

### Current
- Processor desgin related.
  - [ ] use BRAM for the registers R.
  - [ ] simplify the Jump related instructions, produce a singal (Jump:bool) and address if T in the EX stage, instead of doing in IF.
 
- HOL4 processor model.
  - [ ] use non-blocking assignment for most variables, because of the single module. 



### Long term
- [ ] optimaze the compliation time (mainly generate the *tstate*), which now uses more than 500s.
