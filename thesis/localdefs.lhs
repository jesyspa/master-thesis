%% Types
%format EncScheme        = "\D{EncScheme}"
%format SimpleEavAdv     = "\D{SimpleEAVAdv}"
%format SimpleCPAAdv     = "\D{SimpleCPAAdv}"
%format BitVec           = "\D{BitVec}"
%format Probability      = "\D{Probability}"
%format Semiring         = "\D{Semiring}"
%format Ord              = "\D{Ord}"
%format Dist             = "\D{Dist}"
%format ListDist         = "\D{ListDist}"
%format StateDist        = "\D{StatefulDist}"
%format Writer           = "\D{Writer}"
%format StateT           = "\D{StateT}"
%format MaybeT           = "\D{MaybeT}"
%format ProbabilityProps = "\D{ProbabilityProps}"
%format top              = "\D{$\top$}"
%format bot              = "\D{$\bot$}"
%format AdvState         = "\D{AdvState}"
%format OracleState      = "\D{OracleState}"
%format OracleArg        = "\D{OracleArg}"
%format OracleResult     = "\D{OracleResult}"
%format OracleInit       = "\D{OracleInit}"
%format Adversary        = "\D{Adversary}"

%% Constructors
%format encscheme    = "\IC{enc-scheme}"
%format simpleeavadv = "\IC{simple-eav-adv}"
%format simplecpaadv = "\IC{simple-cpa-adv}"

%% Record fields
%format enc            = "\RF{enc}"
%format keygen         = "\RF{keygen}"
%format A1             = "\RF{A\textsubscript{1}}"
%format A2             = "\RF{A\textsubscript{2}}"
%format supersemiring  = "\RF{super-semiring}"
%format superord       = "\RF{super-ord}"
%format one            = "\RF{one}"
%format zro            = "\RF{zro}"
%format neg            = "\RF{neg}"
%format Return         = "\RF{Return}"
%format Uniform        = "\RF{Uniform}"
%format GetState       = "\RF{GetState}"
%format SetState       = "\RF{SetState}"
%format GetAdvState    = "\RF{GetAdvState}"
%format SetAdvState    = "\RF{SetAdvState}"
%format InitOracle     = "\RF{InitOracle}"
%format CallOracle     = "\RF{CallOracle}"
%format GetOracleState = "\RF{GetOracleState}"
%format SetOracleState = "\RF{SetOracleState}"
%format Repeat         = "\RF{Repeat}"

%% CryptoExpressions
%format CryptoExpr       = "\D{CryptoExpr}"
%format uniformexpr      = "\F{uniform-expr}"
%format coinexpr         = "\F{coin-expr}"
%format fmapCE           = "\F{fmap-CE}"
%format bindCE           = "\F{bind-CE}"
%format evalCE           = "\F{eval-CE}"
%format uniformCE        = "\F{uniform-CE}"
%format coinCE           = "\F{coin-CE}"
%format setStateCE       = "\F{setState-CE}"
%format getStateCE       = "\F{getState-CE}"
%format setAdvStateCE    = "\F{setAdvState-CE}"
%format getAdvStateCE    = "\F{getAdvState-CE}"
%format initOracleCE     = "\F{initOracle-CE}"
%format callOracleCE     = "\F{callOracle-CE}"
%format OracleExpr       = "\D{OracleExpr}"
%format setOracleStateCE = "\F{setOracleState-CE}"
%format getOracleStateCE = "\F{getOracleState-CE}"

%format OracleImpl      = "\D{OracleImpl}"
%format InitImpl        = "\RF{InitImpl}"
%format CallImpl        = "\RF{CallImpl}"

%format BoundOracleUse  = "\D{BoundOracleUse}"
%format ReturnBOU       = "\RF{ReturnBOU}"
%format UniformBOU      = "\RF{UniformBOU}"
%format GetAdvStateBOU  = "\RF{GetAdvStateBOU}"
%format SetAdvStateBOU  = "\RF{SetAdvStateBOU}"
%format InitOracleBOU   = "\RF{InitOracleBOU}"
%format CallOracleBOU   = "\RF{CallOracleBOU}"
%format hasBOU          = "\F{has-BOU?}"
%format hasBOUsound     = "\F{has-BOU?-Sound}"

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
%format uniforminterchange = "\F{uniform-interchange}"

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
%format left        = "\F{left}"
%format right       = "\F{right}"
%format graphAt     = "\F{graphAt}"
%format ingraph     = "\F{ingraph}"

%% Indexed monads
%format IxFunctor      = "\D{IxFunctor}"
%format IxMonad        = "\D{IxMonad}"
%format ixfunctorsuper = "\RF{ixfunctor-super}"
%format fmapi          = "\RF{fmap\textsuperscript{i}}"
%format bindi          = "\RF{$>\!>\!=$\textsuperscript{i}}"
%format joini          = "\RF{join\textsuperscript{i}}"
%format returni        = "\RF{return\textsuperscript{i}}"
%format _=>_           = "\F{\_$\Rightarrow$\_}"
%format =>             = "\F{$\Rightarrow$}"
%format _~>_           = "\F{\_$\rightsquigarrow$\_}"
%format ~>             = "\F{$\rightsquigarrow$}"

%% Command Structures
%format CommandStructure         = "\D{CommandStructure}"
%format CmdMorphism              = "\D{CmdMorphism}"
%format CmdStruct                = "\D{CmdStruct}"
%format Conjugate                = "\D{Conjugate}"
%format Forget                   = "\D{Forget}"
%format C1                       = "C_1"
%format C2                       = "C_2"
%format CommandAlgebra           = "\F{CommandAlgebra}"
%format MonadicCommandAlgebra    = "\F{MonadicCommandAlgebra}"
%format foldalgebra              = "\F{fold-algebra}"
%format idAlg                    = "\F{id-Alg}"
%format demonadisealgebra        = "\F{demonadise-algebra}"
%format foldmonadicalgebra       = "\F{fold-monadic-algebra}"
%format fmapCSMAlg               = "\F{fmap-CS-MAlg}"
%format fmapCSFM                 = "\F{fmap-CS-FM}"

%% Interaction Structures
%format InteractionStructure = "\D{InteractionStructure}"
%format ISMorphism           = "\D{ISMorphism}"
%format IStruct              = "\D{IStruct}"
%format Command              = "\RF{Command}"
%format Response             = "\RF{Response}"
%format next                 = "\RF{next}"
%format CommandF             = "\RF{CommandF}"
%format ResponseF            = "\RF{ResponseF}"
%format nextF                = "\RF{nextF}"
%format TensorUnitIS         = "\D{$1$}"
%format S1                   = "S_1"
%format S2                   = "S_2"
%format s1                   = "s_1"
%format s2                   = "s_2"
%format IS1                  = "I\!S_1"
%format IS2                  = "I\!S_2"

%% Free Monads
%format FreeMonad            = "\D{FreeMonad}"
%format ReturnFM             = "\F{Return-FM}"
%format InvokeFM             = "\F{Invoke-FM}"
%format fmapFM               = "\F{fmap-FM}"
%format apFM                 = "\F{ap-FM}"
%format bindFM               = "\F{bind-FM}"

%% Not sure where to put
%format Injective = "\F{Injective}"

%% Infix operator standalones
%format _+_ = "\F{\_\hspace{-0.1em}+\hspace{-0.1em}\_}"
%format _*_ = "\F{\_\hspace{-0.1em}*\hspace{-0.1em}\_}"
%format _<_ = "\F{\_\hspace{-0.1em}\textless\hspace{-0.1em}\_}"
%format _oplus_ = "\F{\_\hspace{-0.1em}$\oplus$\hspace{-0.1em}\_}"
%format _qoplus_ = "\F{\_\hspace{-0.1em}$\oplus/\sim$\hspace{-0.1em}\_}"

%% Punctuation
%format dot   = "\hspace{-0.3em}.\,"
%format comma = "\hspace{-0.3em},"
%format langle = "\langle"
%format rangle = "\rangle"

%% Misc stuff
%format (plus (a) (b))  = "{" a "}\mathbin{\F{+}}{" b "}"
%format (times (a) (b)) = "{" a "}\mathbin{\F{$\cdot$}}{" b "}"
%format oplus (a) (b) = "{" a "}\mathbin{\F{$\oplus$}}{" b "}"
%format qoplus (a) (b) = "{" a "}\mathbin{\F{$\oplus/\sim$}}{" b "}"
%format (VAL (a))       = "\llbracket {" a "} \rrbracket"

%% Things annoying to :Align
%format ==E = "\F{$\equiv^E$}"
%format ==eE = "\F{$\equiv_\epsilon^E$}"
%format ==e1E = "\F{$\equiv_{\epsilon_1}^E$}"
%format ==e2E = "\F{$\equiv_{\epsilon_2}^E$}"
%format ==eeE = "\F{$\equiv_{\epsilon_1 + \epsilon_2}^E$}"
%format ==D = "\F{$\equiv^D$}"
%format ==eD = "\F{$\equiv_\epsilon^D$}"
%format ==e1D = "\F{$\equiv_{\epsilon_1}^D$}"
%format ==e2D = "\F{$\equiv_{\epsilon_2}^D$}"
%format ==eeD = "\F{$\equiv_{\epsilon_1 + \epsilon_2}^D$}"
%format eq (a) (b) = "{" a "}\mathbin{\F{==}}{" b "}"
%format congbind = "\F{cong-\textgreater\!\!\textgreater\!=}"
