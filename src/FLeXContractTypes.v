Require Import UMLang.SolidityNotations2. 

Module FLeXContractTypes (xt: XTypesSig).

Import xt.

Definition XHandle   := XAddress . 
Definition XQueue    := XList .
Definition XBigQueue := XList .
Definition XBytes    := XList .

End FLeXContractTypes.