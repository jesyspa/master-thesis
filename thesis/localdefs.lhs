%% Types
%format CryptoExpr       = "\D{CryptoExpr}"
%format EncScheme        = "\D{EncScheme}"
%format SimpleEavAdv     = "\D{SimpleEAVAdv}"
%format SimpleCPAAdv     = "\D{SimpleCPAAdv}"
%format BitVec           = "\D{BitVec}"
%format Probability      = "\D{Probability}"
%format Semiring         = "\D{Semiring}"
%format Ord              = "\D{Ord}"
%format ListDist         = "\D{ListDist}"
%format Writer           = "\D{Writer}"
%format ProbabilityProps = "\D{ProbabilityProps}"
%format top              = "\D{$\top$}"
%format bot              = "\D{$\bot$}"
%format AdvState         = "\D{AdvState}"
%format OracleState      = "\D{OracleState}"
%format OracleArg        = "\D{OracleArg}"
%format OracleResult     = "\D{OracleResult}"
%format Adversary        = "\D{Adversary}"

%% Constructors
%format encscheme    = "\IC{enc-scheme}"
%format simpleeavadv = "\IC{simple-eav-adv}"
%format simplecpaadv = "\IC{simple-cpa-adv}"

%% Record fields
%format enc           = "\RF{enc}"
%format keygen        = "\RF{keygen}"
%format A1            = "\RF{A\textsubscript{1}}"
%format A2            = "\RF{A\textsubscript{2}}"
%format supersemiring = "\RF{super-semiring}"
%format superord      = "\RF{super-ord}"
%format one           = "\RF{one}"
%format zro           = "\RF{zro}"
%format neg           = "\RF{neg}"
%format Return        = "\RF{Return}"
%format Uniform       = "\RF{Uniform}"
%format GetAdvState   = "\RF{GetAdvState}"
%format SetAdvState   = "\RF{SetAdvState}"
%format InitOracle    = "\RF{InitOracle}"
%format CallOracle    = "\RF{CallOracle}"

%% CryptoExpressions
%format uniformexpr     = "\F{uniform-expr}"
%format coinexpr        = "\F{coin-expr}"
%format fmapCE          = "\F{fmap-CE}"
%format bindCE          = "\F{bind-CE}"
%format uniformCE       = "\F{uniform-CE}"
%format coinCE          = "\F{coin-CE}"
%format setAdvStateCE   = "\F{setAdvState-CE}"
%format getAdvStateCE   = "\F{getAdvState-CE}"
%format initOracleCE    = "\F{initOracle-CE}"
%format callOracleCE    = "\F{callOracle-CE}"

%% Games
%format G1           = "G\textsubscript{1}"
%format G2           = "G\textsubscript{2}"
%format simpleINDEAV = "\F{simple-IND-EAV}"
%format simpleINDCPA = "\F{IND-CPA}"
%format OTPINDCPA    = "\F{OTP-IND-CPA}"
%format OTPINDCPAADV = "\F{OTP-IND-CPA-ADV}"

%% Dist features
%format coin = "\F{coin}"
%format uniform = "\F{uniform}"

%% Helper functions
%format sample      = "\F{sample}"
%format interchange = "\F{interchange}"
%format xor a b     = "{" a "}\mathbin{\F{$\otimes$}}{" b "}"
%format isYes       = "\F{isYes}"
%format fmap        = "\F{fmap}"
%format negpow2     = "\F{negpow2}"
%format compare     = "\F{compare}"
%format embed       = "\F{embed}"
%format pow2        = "\F{pow2}"
%format allzero     = "\F{all-zero}"
%format allone      = "\F{all-one}"
%format vxor        = "\F{vxor}"
%format fst         = "\F{fst}"
%format snd         = "\F{snd}"

%% Not sure where to put
%format Injective = "\F{Injective}"

%% Infix operator standalones
%format _+_ = "\F{\_\hspace{-0.1em}+\hspace{-0.1em}\_}"
%format _*_ = "\F{\_\hspace{-0.1em}*\hspace{-0.1em}\_}"
%format _<_ = "\F{\_\hspace{-0.1em}\textless\hspace{-0.1em}\_}"

%% Punctuation
%format dot   = "\hspace{-0.3em}.\,"
%format comma = "\hspace{-0.3em},"
%format langle = "\langle"
%format rangle = "\rangle"

%% Misc stuff
%format (plus (a) (b))  = "{" a "}\mathbin{\RF{+}}{" b "}"
%format (times (a) (b)) = "{" a "}\mathbin{\RF{$\cdot$}}{" b "}"
%format (VAL (a))       = "\llbracket {" a "} \rrbracket"

%% Things annoying to :Align
%format ==D = "\F{$\equiv_D$}"
%format eq (a) (b) = "{" a "}\mathbin{\F{==}}{" b "}"
%format congbind = "\F{cong-\textgreater\!\!\textgreater\!=}"
