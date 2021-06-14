P2 demo prep

Display with: M-x toggle-truncate-lines

P2 demo

JSON_Validate proved memory safe assuming the following
* abstracted due to bit logical operations
    * countHighBits: we will come back to this
    * skipUTF8
    * skipUTF8MultiByte
* simplified bit arithmetic:
    * shortestUTF8
* replaced integer arithmetic:
    * skipDigits

Found one integer overflow cbmc can't find, maybe some other issues

Proof status: See ../../TODO.md

Function contracts generally look similar: skipSpace contract and loop invariant
  * verifast: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L115
  * cbmc: https://github.com/ArenBabikian/coreJSON/blob/8614b8670a86ade93b5b49cc061ae19cf9ba587f/source/core_json.c#L64

Some differences over being able to prove start<=max: skipDigits
  * verifast: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L910
  * cbmc: https://github.com/ArenBabikian/coreJSON/blob/8614b8670a86ade93b5b49cc061ae19cf9ba587f/source/core_json.c#L700
  * see verifast issue (div) https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L948

Some proofs not required for cbmc:
  * skipHexExcape: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L532
  * skipOneHexEscape: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L441
  * see loop invariant: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L480

Some issues
  * bitwise logical operations (much discussed, see below)
  * integer arithmetic (skipDigits)
  * union:
      * see union: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L81
      * see hexToInt: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L390
  * literals:
      * see skipLiteral: https://github.com/FreeRTOS/coreJSON/blob/5c678b2545c1aeb889586863f75e74af3b8ef924/source/core_json.c#L600
      * see skipAnyLiteral: https://github.com/FreeRTOS/coreJSON/blob/5c678b2545c1aeb889586863f75e74af3b8ef924/source/core_json.c#L634
      * see skipAnyLiteral verifast code: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L852
  * integer bounds:
      * see nextValue: https://github.com/markrtuttle/coreJSON/blob/a3fe2ebde672daeae3230a1cce65d0fb9de21570/source/core_json.c#L1632
  * bitwise logical operations:
      * See countHighBits demos
  * possible to get "success" with 0x0




Invoke Verifast with `verifast -target 32bit -prover z3v4.5 -shared FILE.c`.

As of June 10, 2021,
* countHighBits1.c: 0m0.290s
* countHighBits2.c: 0m0.153s
* countHighBits3.c: 0m36.872s
* countHighBits4.c: 0m11.698s
