%% Types
%format CryptoExpr   = "\D{CryptoExpr}"
%format EncScheme    = "\D{EncScheme}"
%format SimpleEavAdv = "\D{SimpleEAVAdv}"
%format SimpleCPAAdv = "\D{SimpleCPAAdv}"
%format BitVec       = "\D{BitVec}"
%format Probability  = "\D{Probability}"
%format Semiring     = "\D{Semiring}"
%format Ord          = "\D{Ord}"

%% Constructors
%format encscheme    = "\IC{enc-scheme}"
%format simpleeavadv = "\IC{simple-eav-adv}"
%format simplecpaadv = "\IC{simple-cpa-adv}"

%% Record fields
%format enc    = "\RF{enc}"
%format keygen = "\RF{keygen}"
%format A1     = "\RF{A\textsubscript{1}}"
%format A2     = "\RF{A\textsubscript{2}}"
%format supersemiring = "\RF{super-semiring}"
%format superord = "\RF{super-ord}"

%% CryptoExpressions
%format uniformexpr = "\F{uniform-expr}"
%format coinexpr    = "\F{coin-expr}"

%% Games
%format G1           = "G\textsubscript{1}"
%format G2           = "G\textsubscript{2}"
%format simpleINDEAV = "\F{simple-IND-EAV}"
%format simpleINDCPA = "\F{IND-CPA}"

%% Dist features
%format coin = "\F{coin}"
%format uniform = "\F{uniform}"

%% Helper functions
%format sample                    = "\F{sample}"
%format interchangeinterpretation = "\F{interchange-interpretation}"
%format xor a b                   = "{" a "}\mathbin{\F{$\otimes$}}{" b "}"
%format isYes                     = "\F{isYes}"
%format fmap                      = "\F{fmap}"
%format negpow2                   = "\F{negpow2}"
%format compare                   = "\F{compare}"
%format zro                       = "\F{zro}"
%format one                       = "\F{one}"

%% Infix operator standalones
%format _+_ = "\F{\_\hspace{-0.1em}+\hspace{-0.1em}\_}"
%format _*_ = "\F{\_\hspace{-0.1em}*\hspace{-0.1em}\_}"
%format _<_ = "\F{\_\hspace{-0.1em}\textless\hspace{-0.1em}\_}"

%% Punctuation
%format dot   = "\hspace{-0.3em}.\,"
%format comma = "\hspace{-0.3em},"

%% Misc stuff
%format (plus (a) (b))  = "{" a "}\mathbin{\F{+}}{" b "}"
%format (times (a) (b)) = "{" a "}\mathbin{\F{$\cdot$}}{" b "}"
%format (VAL (a))       = "\llbracket {" a "} \rrbracket"

%% Things annoying to :Align
%format ==D = "\F{$\equiv^D$}"
%format eq (a) (b) = "{" a "}\mathbin{\F{==}}{" b "}"
%format congbind = "\F{cong-\textgreater\!\!\textgreater\!=}"
