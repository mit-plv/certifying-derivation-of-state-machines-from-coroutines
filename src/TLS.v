Require Import List.
Require Import Inhabit Foldable ClConv.
Import ListNotations.

Definition byte := Ascii.ascii.
Definition string := list byte.

Inductive Group := P256 | P384 | P521 | X25519.

Inductive PskMode := pskModePlain | PskModeDHE.

Inductive SignatureScheme :=
  PKCS1WithSHA256
| PKCS1WithSHA384
| PKCS1WithSHA512
| PSSWithSHA256
| PSSWithSHA384
| PSSWithSHA512
| ECDSAWithP256AndSHA256
| ECDSAWithP384AndSHA384
| ECDSAWithP512AndSHA512
| Ed25519
| PKCS1WithSHA1
| ECDSAWithSHA1.

Scheme Equality for Group.
Scheme Equality for PskMode.
Scheme Equality for SignatureScheme.

(*
Definition defaultCurvePreference :=
  [X25519; CurveP256; CurveP384; CurveP521].
 *)

Record KeyShare :=
  { KSgroup : Group;
    KSdata : string
  }.

Record PskIdentity :=
  { PIlabel : list byte;
    PIobfuscatedTicketAge : nat
  }.

Record Certificate :=
  { Ccertificate : list (list byte);
    CprivateKey : list byte;
    COSPStable : list byte;
    CSignedCertificateTimestamps : list (list byte);
    CLeaf : list byte
  }.

Record SessionStateTLS13 :=
  { STcipherSuite : nat;
    STcreatedAt : nat;
    STresumptionSecret : list byte;
    certificate : Certificate
  }.

(*
Record ServerHelloMsg :=
  { (* SHlegacy_version : nat;*)
    SHrandom : list byte;
(*     SHlegacy_sessionID : list nat;*)
    SHcipherSuite : nat;
(*    SHlegacy_compressionMethod : nat; *)
    SHsupportedVersion : nat;
    SHserverShare : option KeyShare;
    SHselectedCurve : option CurveID
  }.
*)

Parameter ExtensionRaw : Set.
Record ClientHelloMsg :=
  {
    CHextension : list ExtensionRaw;
  }.

(*
  { (* CHlegacy_version_ : nat;*)
    CHrandom : list byte;
(*    CHlegacy_sessionID : list nat; *)
    CHcipherSuites : list byte;
(*    CHlegacy_compressionMethod : nat; *)
    CHsupportedCurves : list CurveID;
    CHkeyShares : list KeyShare;
    CHpskModes : list nat;
    CHpskIdentities : list PskIdentity;
    CHserverName : String.string;
    CHsupportedSignatureAlgorithms : list SignatureScheme
  }.
*)

Record CipherSuiteTLS13 :=
  { CSid : nat;
    CSkeyLen : nat;
  }.

(*
Record ServerHandshakeState :=
  { SHSclientHello : ClientHelloMsg;
    SHSserverHello : ServerHelloMsg
  }.
*)
Parameter curve25519_scalarBaseMult : list byte -> list byte.
Parameter curve25519_scalarMult : list byte -> list byte -> list byte.
(*
Parameter scalarMult : CurveID -> nat -> nat -> list byte -> list byte.
Parameter scalarBaseMult : CurveID -> list byte -> nat * nat.
Parameter elliptic_Marshal : CurveID -> nat * nat -> list byte.
Parameter elliptic_Unmarshal : CurveID -> list byte -> nat * nat.
Parameter paramSize : CurveID -> nat.
Parameter nat_to_byte : nat -> byte.

Parameter clientHelloMsg_marshal : ClientHelloMsg -> list byte.
Parameter serverHelloMsg_marshal : ServerHelloMsg -> list byte.

Parameter sessionStateTLS13_marshal : SessionStateTLS13 -> list byte.
Parameter sessionStateTLS13_unmarshal : list byte -> SessionStateTLS13.

Parameter VersionTLS13 : nat.
Parameter helloRetryRequestRandom : list byte.

Parameter decryptTicket : list byte -> list byte.

Parameter signatureSchemesForCertificate :
  nat -> Certificate -> list SignatureScheme.

Definition typeMessageHash := (0,(1,(1,(1,(1,(1,(1,1))))))).

Parameter hash : list byte -> list byte.
*)
(*
Definition doHelloRetryRequest (ch : ClientHelloMsg)(sh : ServerHelloMsg)
           (selectedCurve : CurveID) :=
  let chHash := hash (clientHelloMsg_marshal ch) in
  let helloRetryRequest :=
      { SHrandom := helloRetryRequestRandom;
        SHcipherSuite := sh.(SHcipherSuite);
        SHsupportedVersion := sh.(SHsupportedVersion);
        SHserverShare := None;
        SHselectedCurve := selectedCurve }
  in
  let transcript :=
      typeMessageHash :: x00 :: x00 :: nat_to_byte (length chHash)
                      :: chHash ++ serverHelloMsg_marshal helloRetryRequest
  in
  
  c <- writeRecord (serverHelloMsg_marshal helloRetryRequest);
    sendDummyChangeCipherSpec;
    msg <- readHandshake c;
    let clientHello := msg.(ClientHelloMsg) in
    match clientHello.(CHkeyShares) with
    | [ks] =>
      if not (CurveID_beq ks.(KSgroup) selectedCurve) then
        Return (inr "Client sent invalid key share in second ClientHello")
      else
        (* ... *)
        Return (inl clientHello)
*)

Ltac nth_of_tuple' p n flag :=
  lazymatch n with
  | O =>
    lazymatch flag with
    | true => exact p
    | false => exact (snd p)
    end
  | S ?n' => nth_of_tuple' (fst p) n' flag
  end.

Ltac nth_of_tuple p n :=
  let ty := type of p in
  let rec aux ty :=
      lazymatch ty with
      | ?ty' * _ => let v := aux ty' in constr:(S v)
      | _ => O
      end
  in
  let m := aux ty in
  let n' := (eval simpl in (m - n)) in
  lazymatch n with
  | O => nth_of_tuple' p n' true
  | _ => nth_of_tuple' p n' false
  end.

Notation "p ._( n )" :=
  ltac:(nth_of_tuple p n)
         (at level 0, only parsing).

(*
Definition elliptic_GenerateKey (curve : CurveID) :=
  private <- getRnd;
    let public := scalarBaseMult curve private in
    Return (private,public).
*)

Parameter ServerParams : Set.
Parameter Context : Set.

Parameter serverGroups : Context -> list Group.

Fixpoint findKeyShare ks gs :=
  match gs with
  | [] => None
  | g::gs' =>
    match find (fun k => Group_beq (KSgroup k) g) ks with
    | Some k => Some k
    | None => findKeyShare ks gs'
    end
  end.

Definition intersect (xs ys : list Group) :=
  filter (fun x => if in_dec Group_eq_dec x ys then true else false) xs.

Parameter extension_KeyShare : list ExtensionRaw -> option (list KeyShare).
Parameter extension_NegotiatedGroups : list ExtensionRaw -> list Group.

Inductive eff_tls := recvClientHello | generateRND.

Definition args_tls ef :=
  match ef with
  | recvClientHello => Context
  | generateKey => unit
  end.

Definition rets_tls ef :=
  match ef with
  | recvClientHello => ClientHelloMsg
  | generateKey => string
  end.

Definition lift_tls A B(e : eff_tls)(a : rets_tls e -> A + option B) e0
  : rets_tls e0 -> A + option B :=
  match
  e as e1
  return ((rets_tls e1 -> A + option B) -> rets_tls e0 -> A + option B)
  with
  | recvClientHello =>
    fun a0 : rets_tls recvClientHello -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | recvClientHello => a0
      | _ => fun _ => inr None
      end
  | generateRND =>
    fun a0 : rets_tls generateRND -> A + option B =>
      match e0 as e1 return (rets_tls e1 -> A + option B) with
      | generateRND => a0
      | _ => fun _ => inr None
      end
  end a.

Instance eff_tls_is_eff : is_eff eff_tls :=
  { args := args_tls;
    rets := rets_tls;
    lift_eff := lift_tls }.

Notation "ch <-recvClientHello ctx ; p" :=
  (@Eff eff_tls args_tls rets_tls _ recvClientHello ctx (fun ch => p))
    (at level 100, right associativity).

Definition pickKeyShare
           (ctx : Context) :=
  ch <-recvClientHello ctx;
    match extension_KeyShare ch.(CHextension) with
    | None => Return None
    | Some keyShares =>
      match findKeyShare keyShares (serverGroups ctx) with
      | None =>
        (* helloRetryRequest *)
        let clientGroups := extension_NegotiatedGroups ch.(CHextension) in
        let possibleGroups := intersect (serverGroups ctx) clientGroups in
        match hd_error possibleGroups with
        | None => Return None
        | Some g => 
          ch' <-recvClientHello ctx;
            match extension_KeyShare ch'.(CHextension) with
            | None => Return None
            | Some keyShares =>
              match findKeyShare keyShares (serverGroups ctx) with
              | None => Return None
              | Some keyShare => Return (Some (ch', keyShare))
              end
            end
        end
      | Some keyShare => Return (Some (ch, keyShare))
      end
    end.

Definition pickKeyShare_derive :
  { state & { step & forall ctx,
                { init | @equiv _ _ _ _ state step init (pickKeyShare ctx) }}}.
Proof.
  do 3 eexists.
  unfold pickKeyShare.
  derive' (tt,ctx).
Defined.

Definition pickKeyShare_step := Eval cbv [projT1 projT2 pickKeyShare pickKeyShare_derive] in (fun ctx => projT1 (projT2 pickKeyShare_derive) ctx).

Extract Inductive unit => "()" [ "()" ].
Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive bool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive sumbool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Inductive option => "GHC.Base.Maybe" ["GHC.Base.Just" "GHC.Base.Nothing"].
Extract Inductive Group => "T.Group" ["T.P256" "T.P384" "T.P521" "T.X25519"].
Extract Constant Group_eq_dec => "(==)".
Extract Constant Group_beq => "(==)".
Extract Constant Context => "T.Context".
Extract Constant ExtensionRaw => "I.ExtensionRaw".
Extract Constant string => "B.ByteString".
Extract Constant extension_KeyShare => "Helper.extension_KeyShare".
Extract Constant extension_NegotiatedGroups => "Helper.extension_NegotiatedGroups".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Inductive KeyShare => "Helper.KeyShare" ["Helper.Build_KeyShare"].

Require Extraction.
Extraction Language Haskell.

Extraction "TLS.hs" pickKeyShare_step.

(*
srand <- getRnd;
          protoExt <<- applicationProtocol ctx exts sparams
                   (psk,binderInfo,is0RTTvalid) <<- choosePSK;
          earlyKey <- calculateEarlySecret ctx choice (inl psk) true;
          let earlySecret := pairBase earlyKey in
                let clientEarlySecret := pairClient earlyKey in
                
    end
  end
*)

Definition processClientHello (ch : ClientHelloMsg) :=
  random <- getRnd;
    let ks :=
        list_rec_nondep
          (fun opt =>
             match opt with
             | Some group =>
               Some (doHelloRetryRequest group)
             | None => None
             end)
          (fun preferredGroup restCurves recPref opt =>
             list_rec_nondep
               (match opt with
                | Some group => recPref opt
                | None =>
                  if in_dec CurveID_eq_dec
                            preferredGroup ch.(CHsupportedCurves) then
                    recPref (Some preferredGroup)
                  else
                    recPref None
                end)
               (fun ks keyShares' rec =>
                  if CurveID_beq ks.(KSgroup) preferredGroup then
                    Some ks
                  else
                    rec)
               ch.(CHkeyShares))
          defaultCurvePreference
          None
    in
    match ks with
    | Some clientKeyShare =>
      keys <<- (if CurveID_beq clientKeyShare.(KSgroup) X25519 then
                  private <- getRnd;
                    Return (curve25519_scalarBaseMult private,
                     curve25519_scalarMult private clientKeyShare.(KSdata))
                else
                  let curveID := clientKeyShare.(KSgroup) in
                  keys' <<- elliptic_GenerateKey curveID;
                    Return
                      (elliptic_Marshal curveID (snd keys'),
                       let (x,y) :=
                           elliptic_Unmarshal curveID clientKeyShare.(KSdata)
                       in
                       scalarMult curveID x y (fst keys'))
               );
      let share :=
          {| KSgroup := clientKeyShare.(KSgroup);
             KSdata := keys._(0) |}
      in
      Return (Some ({| SHrandom := random;
                      SHcipherSuite := 0;
                      SHsupportedVersion := VersionTLS13;
                      SHserverShare := Some share;
                      SHselectedCurve := Some share.(KSgroup) |},
                   keys._(1)))
    | None =>
      Return None
        (*(inr "No ECDHE curve supported by both client and server")*)
    end.

Definition processClientHello_derive :
  { state & { step & forall ch,
                { init | @equiv _ _ _ _ state step init (processClientHello ch) }}}.
Proof.
  do 3 eexists.
  unfold processClientHello.
  derive' (tt,ch).
Defined.

Eval cbv [projT1 projT2 processClientHello processClientHello_derive] in (fun ch => projT1 (projT2 processClientHello_derive) ch).

Parameter getCertificate : String.string -> Map Certificate -> list Certificate -> option Certificate.

(*
Definition getCertificate
           (serverName : Stirng.string)
           (nameToCertificate : Map Certificate)
           (certificates : list Certificate) :=
  (* if c.GetCertificate != nil ... *)
  match certificates with
  | [] => None
  | cerf::[] => Some cerf
  | cerf::_ =>
    let name := toLower serverName in
    match bsearch name nameToCertificate with
    | Some cerf' => Some cerf'
    | None =>
 *)

Definition pickCertificate
           (clientHello : ClientHelloMsg)
           (serverHello : ServerHelloMsg)
           (usingPSK : bool)
           (hs : ServerHandshakeState)
           (nameToCertificate : Map Certificate)
           (certificates : list Certificate) :=
  if usingPSK then
    None
  else
    match getCertificate clientHello.(CHserverName) nameToCertificate certificates with
    | None => None
    | Some certificate =>
      let supportedAlgs :=
          signatureSchemesForCertificate hs.(SHSserverHello).(SHsupportedVersion) certificate
      in
      list_rec_nondep
        None
        (fun preferredAlg rest aux =>
           if in_dec SignatureScheme_eq_dec preferredAlg supportedAlgs then
             Some preferredAlg
           else
             aux)
        clientHello.(CHsupportedSignatureAlgorithms)
    end.


Definition checkForResumption (ch : ClientHelloMsg) suite :=
  if in_dec PskMode_eq_dec PskModeDHE ch.(CHpskModes) then
    list_rec_nondep
      (Return None)
      (fun identity rec =>
         let plaintext := decryptTicket identity.(label) in
         let sessionState := sessionStateTLS13_unmarshal plaintext in
         let pskSuite := cipherSuiteTLS13ByID sessionState.(cipherSuite) in
         if pskSuite.(hash)!= suite.(hash) then
           rec
         else
           let sessionHasClientCerts :=
               notb (Nat.eqb (sessionState.(certificate).(Certificate)) 0)
           in
           let needClientCerts :=
               requiresClientCert c.(config).(ClientAuth)
           in
           if (needClientCerts && notb sessionHasClientCerts)
              || (sessionHasClientCerts && c.(config).(ClientAuth) == NoClientCert) then
             rec
           else
             Return (Some (extract suite))
      )
      ch.(CHpskIdentities)
  else Return None.