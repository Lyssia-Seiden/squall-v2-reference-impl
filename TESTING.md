# Design-verification programs

`zig build hex -- out` now exports a suite of test programs alongside `fib`,
each into `out/<name>/`. They use the same host calling convention as `fib`
(two entry tokens, result written by `host_return`), so a testbench that runs
`fib` can run these unchanged.

```
zig build hex -- out              # everything
zig build hex -- out 20           # fib (and sum_loop) with input 20
zig build hex -- out - rand_      # only programs whose name starts with rand_
zig build test                    # model vs. hand-computed expectations
```

## Files per program

| file | contents |
|---|---|
| `memory.hex` | initial image, same format as before (`@<word addr> <hex>`) |
| `params.txt` | same keys as before; test programs add `num_checks` and `check_<i> = <label> @<word addr> <value>` |
| `expected.hex` | **new.** every word to compare after the run: all check words, then the result. Same `@addr value` format as `memory.hex` |
| `trace.txt` | **new.** one line per token the model pops: `cycle ip fp port acc` (hex addresses). Tokens to ip 0 are dropped without executing |

`fib`'s `memory.hex` and `params.txt` are byte-identical to before.

## Check words

Besides `result`, each test program writes intermediate values to *check
words* in the image as it runs (a `Write` with ack, inserted after an
instruction). If the RTL disagrees with the model, the first wrong check names
the instruction that misbehaved. Every check word starts as `0xBAD0BAD0BAD0BAD0`
so one the RTL never wrote can't pass by accident.

All check writes are acked into the flow that produces `result`, so every check
is written before the result is; stopping the sim on the result write is safe.

The programs are schedule-independent: every matching slot sees its tokens in an
order fixed by data dependencies, and every value that gets parked in a matching
slot is first normalized to 62 bits (shl 2, shra 2), so RTL that schedules
tokens differently from the model's LIFO stack must still produce the same
words. (`trace.txt` order is
the model's order; if the RTL schedules differently, compare traces sorted.)

## Programs

| program | covers |
|---|---|
| `alu_imm` | every monadic ALU op against an immediate, token on the left and on the right port; signed/unsigned divide, rem vs. mod signs, shift amounts mod 64, sign-extended immediates |
| `alu_second` | second outputs: add carry, sub borrow, mul high word, div/rem/mod flags (div by zero, truncated), Not/Rev/Dupl/Dupr/Nop second values, second-token port |
| `branch_imm` | Beqz/Beql/Beqr/Blel/Bler, both directions each, both token ports, unsigned comparison. The left path adds `0x1000`, the right path `0x2000`, so the check word shows which way it went |
| `alu_dyadic` | the same ops with two runtime operands meeting in frame slots, including second outputs and both branch directions |
| `matching` | frame-, code- and absolute-relative addressing; Once against a preloaded Present word (both ports); Read of untracked words; Const against a preloaded constant (repeated firing); a right token updating a Constant word and firing with the old value; a slot reused after a match clears it; an absolute `Write` read back frame-relatively |
| `write_be` | byte enables (`FF 01 80 F0 0F 5A A5 00`), ack value, two acked writes merging into one word, write to a raw address read back with absolute addressing |
| `call` | Extract minting tags, Send delivering to a minted tag (and to its own d), a call into a child frame at fp + 64 words returning through a passed return tag |
| `mem62` | the 62-bit word format: presence bits in bits [63:62]; sign extension of memory reads (bit 61); Read ignoring and preserving presence bits; a `Write` setting Present/Constant through the top bits; byte enable `0x80` changing only the presence bits and `0x7F` keeping them; a Const update being cut to 62 bits; the minted tag layout `ip[28:0] pad[31:29] fp[60:32] port[61]` for both ports; Send dropping a tag's top two bits (a garbled tag must still land on the right port) |
| `sum_loop` | a loop reusing its matching slots every iteration (result = n(n+1)/2; takes the command-line input) |
| `rand_0001`…`rand_0008` | seeded random 48-step chains mixing monadic ops (random port, random/edge-case immediates, random second outputs), branches, and dyadic Reads of random 64-bit constants (code and absolute). Every step is a check word. Add seeds in `random_seeds` |

Directed programs carry hand-computed expectations written with plain Zig
arithmetic (not `apply_alu`), and `zig build test` checks the model against
them. Random programs' expectations are the model's own output.

## Checked against the model

Besides hand-computed expectations, the suite was checked by breaking the model
on purpose and confirming that a test fails:

| change to the model | caught by |
|---|---|
| undo "adjust padding to match isacomp impl" | `mem62`, check `chk_ext_l` |
| zero-extend memory reads instead of sign-extending | `alu_imm` and others |
| Send keeps the wrong 62 bits of a tag | several programs |
| Read consumes a Present word like Once | `matching` |

## Things the suite turned up about the model

These aren't failures, but the RTL needs an answer for each:

1. **`Div`/`Rem`/`Mod` of `i64` min by `-1`** traps in the model (`@divTrunc`
   overflow). The RTL will produce *something*; the spec should say what. The
   random generator avoids this case.
2. **`Const` matching, left token on an Empty word**: the token is dropped and
   the word written with `undefined`. That makes the result depend on whether
   the constant or the left token arrives first. The suite only uses Const
   words that are preloaded or already Constant.
3. **`Once` matching ignores ports**: two left tokens in one slot pair with
   each other. A loop whose next-iteration token can overtake the current one
   is schedule-dependent (`sum_loop` holds the counter until the new sum
   exists to avoid this).
4. **A parked token loses its top two bits.** When a token waits in a
   matching slot, only its low 62 bits are stored, and its partner later sees
   them sign-extended. So a dyadic op on any value whose bits 63..61 aren't all
   equal gives a different answer depending on which operand arrives first.
   This also applies to `final_send`: a result that doesn't fit in 62 bits,
   arriving before the return tag, reaches the host cut to 62 bits. The suite
   normalizes every parked value to avoid this; real programs would need a
   compiler rule or a hardware answer.
5. **A `Write` of an ordinary value sets presence bits.** Writing any value
   with bit 63 or 62 set changes the word's presence state, so a negative
   number written to a slot that is later matched on turns it Present or
   Constant. Top bits `0b11` (any negative number) give a fourth state that
   `PresenceBits` has no name for: the model's match code has no case for it,
   and in Zig, turning those bits into the enum is illegal behaviour. The
   spec should say what the hardware does.
6. **Matched words are written with `undefined`** when cleared, so frame memory
   and matched code words aren't comparable between model and RTL. Only compare
   the words in `expected.hex`.
