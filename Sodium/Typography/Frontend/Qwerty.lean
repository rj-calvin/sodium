import Sodium.Typography.Emulator

open Lean Parser Elab Meta Term Tactic PrettyPrinter

namespace Typography

variable {σ}

declare_syntax_cat grapheme
declare_syntax_cat terminal

syntax (name := terminal) &"\n" : terminal

syntax (name := a) "a" : grapheme
syntax (name := b) "b" : grapheme
syntax (name := c) "c" : grapheme
syntax (name := d) "d" : grapheme
syntax (name := e) "e" : grapheme
syntax (name := f) "f" : grapheme
syntax (name := g) "g" : grapheme
syntax (name := h) "h" : grapheme
syntax (name := i) "i" : grapheme
syntax (name := j) "j" : grapheme
syntax (name := k) "k" : grapheme
syntax (name := l) "l" : grapheme
syntax (name := m) "m" : grapheme
syntax (name := n) "n" : grapheme
syntax (name := o) "o" : grapheme
syntax (name := p) "p" : grapheme
syntax (name := q) "q" : grapheme
syntax (name := r) "r" : grapheme
syntax (name := s) "s" : grapheme
syntax (name := t) "t" : grapheme
syntax (name := u) "u" : grapheme
syntax (name := v) "v" : grapheme
syntax (name := w) "w" : grapheme
syntax (name := x) "x" : grapheme
syntax (name := y) "y" : grapheme
syntax (name := z) "z" : grapheme

syntax (name := A) "A" : grapheme
syntax (name := B) "B" : grapheme
syntax (name := C) "C" : grapheme
syntax (name := D) "D" : grapheme
syntax (name := E) "E" : grapheme
syntax (name := F) "F" : grapheme
syntax (name := G) "G" : grapheme
syntax (name := H) "H" : grapheme
syntax (name := I) "I" : grapheme
syntax (name := J) "J" : grapheme
syntax (name := K) "K" : grapheme
syntax (name := L) "L" : grapheme
syntax (name := M) "M" : grapheme
syntax (name := N) "N" : grapheme
syntax (name := O) "O" : grapheme
syntax (name := P) "P" : grapheme
syntax (name := Q) "Q" : grapheme
syntax (name := R) "R" : grapheme
syntax (name := S) "S" : grapheme
syntax (name := T) "T" : grapheme
syntax (name := U) "U" : grapheme
syntax (name := V) "V" : grapheme
syntax (name := W) "W" : grapheme
syntax (name := X) "X" : grapheme
syntax (name := Y) "Y" : grapheme
syntax (name := Z) "Z" : grapheme

syntax (name := zero) &"0" : grapheme
syntax (name := one) &"1" : grapheme
syntax (name := two) &"2" : grapheme
syntax (name := three) &"3" : grapheme
syntax (name := four) &"4" : grapheme
syntax (name := five) &"5" : grapheme
syntax (name := six) &"6" : grapheme
syntax (name := seven) &"7" : grapheme
syntax (name := eight) &"8" : grapheme
syntax (name := nine) &"9" : grapheme
syntax (name := exclamation) &"!" : grapheme
syntax (name := sign) &"@" : grapheme
syntax (name := hash) &"#" : grapheme
syntax (name := dollar) &"$" : grapheme
syntax (name := percent) &"%" : grapheme
syntax (name := caret) &"^" : grapheme
syntax (name := ampersand) &"&" : grapheme
syntax (name := asterisk) &"*" : grapheme
syntax (name := lparen) &"(" : grapheme
syntax (name := rparen) &")" : grapheme
syntax (name := hyphen) &"-" : grapheme
syntax (name := underscore) &"_" : grapheme
syntax (name := equals) &"=" : grapheme
syntax (name := plus) &"+" : grapheme
syntax (name := lbracket) &"[" : grapheme
syntax (name := rbracket) &"]" : grapheme
syntax (name := lbrace) &"{" : grapheme
syntax (name := rbrace) &"}" : grapheme
syntax (name := slash) &"\\" : grapheme
syntax (name := pipe) &"|" : grapheme
syntax (name := semicolon) &";" : grapheme
syntax (name := colon) &":" : grapheme
syntax (name := apostrophe) &"'" : grapheme
syntax (name := quote) &"\"" : grapheme
syntax (name := comma) &"," : grapheme
syntax (name := period) &"." : grapheme
syntax (name := langle) &"<" : grapheme
syntax (name := rangle) &">" : grapheme
syntax (name := divide) &"/" : grapheme
syntax (name := question) &"?" : grapheme
syntax (name := grave) &"`" : grapheme
syntax (name := tilde) &"~" : grapheme
syntax (name := space) &" " : grapheme

syntax (name := leader) "leader% " (grapheme)? : term
syntax (name := done) "done% " (terminal)? : term

def Terminal := TSyntax `terminal

@[reducible]
def Carriage : Terminal := ⟨mkNode ``terminal #[mkAtom "\n"]⟩

instance : Inhabited Terminal := ⟨Carriage⟩
instance : Encodable Terminal := by unfold Terminal; infer_instance

def newline : Terminal → TermElabM Char
| stx => match stx.raw.getKind with
  | ``terminal => pure '\n'
  | _ => throwUnsupportedSyntax

@[reducible]
def Grapheme := TSyntax `grapheme

@[reducible]
def Space : Grapheme := ⟨mkNode ``space #[mkAtom " "]⟩

instance : Inhabited Grapheme := ⟨Space⟩
instance : Encodable Grapheme := by unfold Grapheme; infer_instance

def parse : Grapheme → TermElabM Char
| `(grapheme|a) => pure 'a'
| `(grapheme|b) => pure 'b'
| `(grapheme|c) => pure 'c'
| `(grapheme|d) => pure 'd'
| `(grapheme|e) => pure 'e'
| `(grapheme|f) => pure 'f'
| `(grapheme|g) => pure 'g'
| `(grapheme|h) => pure 'h'
| `(grapheme|i) => pure 'i'
| `(grapheme|j) => pure 'j'
| `(grapheme|k) => pure 'k'
| `(grapheme|l) => pure 'l'
| `(grapheme|m) => pure 'm'
| `(grapheme|n) => pure 'n'
| `(grapheme|o) => pure 'o'
| `(grapheme|p) => pure 'p'
| `(grapheme|q) => pure 'q'
| `(grapheme|r) => pure 'r'
| `(grapheme|s) => pure 's'
| `(grapheme|t) => pure 't'
| `(grapheme|u) => pure 'u'
| `(grapheme|v) => pure 'v'
| `(grapheme|w) => pure 'w'
| `(grapheme|x) => pure 'x'
| `(grapheme|y) => pure 'y'
| `(grapheme|z) => pure 'z'
| `(grapheme|A) => pure 'A'
| `(grapheme|B) => pure 'B'
| `(grapheme|C) => pure 'C'
| `(grapheme|D) => pure 'D'
| `(grapheme|E) => pure 'E'
| `(grapheme|F) => pure 'F'
| `(grapheme|G) => pure 'G'
| `(grapheme|H) => pure 'H'
| `(grapheme|I) => pure 'I'
| `(grapheme|J) => pure 'J'
| `(grapheme|K) => pure 'K'
| `(grapheme|L) => pure 'L'
| `(grapheme|M) => pure 'M'
| `(grapheme|N) => pure 'N'
| `(grapheme|O) => pure 'O'
| `(grapheme|P) => pure 'P'
| `(grapheme|Q) => pure 'Q'
| `(grapheme|R) => pure 'R'
| `(grapheme|S) => pure 'S'
| `(grapheme|T) => pure 'T'
| `(grapheme|U) => pure 'U'
| `(grapheme|V) => pure 'V'
| `(grapheme|W) => pure 'W'
| `(grapheme|X) => pure 'X'
| `(grapheme|Y) => pure 'Y'
| `(grapheme|Z) => pure 'Z'
| stx => match stx.raw.getKind with
  | ``space => pure ' '
  | ``zero => pure '0'
  | ``one => pure '1'
  | ``two => pure '2'
  | ``three => pure '3'
  | ``four => pure '4'
  | ``five => pure '5'
  | ``six => pure '6'
  | ``seven => pure '7'
  | ``eight => pure '8'
  | ``nine => pure '9'
  | ``exclamation => pure '!'
  | ``sign => pure '@'
  | ``hash => pure '#'
  | ``dollar => pure '$'
  | ``percent => pure '%'
  | ``caret => pure '^'
  | ``ampersand => pure '&'
  | ``asterisk => pure '*'
  | ``lparen => pure '('
  | ``rparen => pure ')'
  | ``hyphen => pure '-'
  | ``underscore => pure '_'
  | ``equals => pure '='
  | ``plus => pure '+'
  | ``lbracket => pure '['
  | ``rbracket => pure ']'
  | ``lbrace => pure '{'
  | ``rbrace => pure '}'
  | ``slash => pure '\\'
  | ``pipe => pure '|'
  | ``semicolon => pure ';'
  | ``colon => pure ':'
  | ``apostrophe => pure '\''
  | ``quote => pure '"'
  | ``comma => pure ','
  | ``period => pure '.'
  | ``langle => pure '<'
  | ``rangle => pure '>'
  | ``divide => pure '/'
  | ``question => pure '?'
  | ``grave => pure '`'
  | ``tilde => pure '~'
  | _ => throwUnsupportedSyntax

elab "leader% " γ:(grapheme)? : tactic => do
  let γ ← parse <| γ.getD default
  let γ := Syntax.mkCharLit γ
  evalTactic <| ← `(tactic|exact ⟨$γ⟩)

elab "done%" : tactic => do
  let γ ← newline default
  let γ := Syntax.mkCharLit γ
  evalTactic <| ← `(tactic|exact ⟨$γ⟩)

section Digits

abbrev Zero : Grapheme := ⟨mkNode ``zero #[mkAtom "0"]⟩
abbrev One : Grapheme := ⟨mkNode ``one #[mkAtom "1"]⟩
abbrev Two : Grapheme := ⟨mkNode ``two #[mkAtom "2"]⟩
abbrev Three : Grapheme := ⟨mkNode ``three #[mkAtom "3"]⟩
abbrev Four : Grapheme := ⟨mkNode ``four #[mkAtom "4"]⟩
abbrev Five : Grapheme := ⟨mkNode ``five #[mkAtom "5"]⟩
abbrev Six : Grapheme := ⟨mkNode ``six #[mkAtom "6"]⟩
abbrev Seven : Grapheme := ⟨mkNode ``seven #[mkAtom "7"]⟩
abbrev Eight : Grapheme := ⟨mkNode ``eight #[mkAtom "8"]⟩
abbrev Nine : Grapheme := ⟨mkNode ``nine #[mkAtom "9"]⟩

end Digits

section Symbols

abbrev Exclamation : Grapheme := ⟨mkNode ``exclamation #[mkAtom "!"]⟩
abbrev Sign : Grapheme := ⟨mkNode ``sign #[mkAtom "@"]⟩
abbrev Hash : Grapheme := ⟨mkNode ``hash #[mkAtom "#"]⟩
abbrev Dollar : Grapheme := ⟨mkNode ``dollar #[mkAtom "$"]⟩
abbrev Percent : Grapheme := ⟨mkNode ``percent #[mkAtom "%"]⟩
abbrev Caret : Grapheme := ⟨mkNode ``caret #[mkAtom "^"]⟩
abbrev Ampersand : Grapheme := ⟨mkNode ``ampersand #[mkAtom "&"]⟩
abbrev Asterisk : Grapheme := ⟨mkNode ``asterisk #[mkAtom "*"]⟩
abbrev Lparen : Grapheme := ⟨mkNode ``lparen #[mkAtom "("]⟩
abbrev Rparen : Grapheme := ⟨mkNode ``rparen #[mkAtom ")"]⟩
abbrev Hyphen : Grapheme := ⟨mkNode ``hyphen #[mkAtom "-"]⟩
abbrev Underscore : Grapheme := ⟨mkNode ``underscore #[mkAtom "_"]⟩
abbrev Equals : Grapheme := ⟨mkNode ``equals #[mkAtom "="]⟩
abbrev Plus : Grapheme := ⟨mkNode ``plus #[mkAtom "+"]⟩
abbrev Lbracket : Grapheme := ⟨mkNode ``lbracket #[mkAtom "["]⟩
abbrev Rbracket : Grapheme := ⟨mkNode ``rbracket #[mkAtom "]"]⟩
abbrev Lbrace : Grapheme := ⟨mkNode ``lbrace #[mkAtom "{"]⟩
abbrev Rbrace : Grapheme := ⟨mkNode ``rbrace #[mkAtom "}"]⟩
abbrev Slash : Grapheme := ⟨mkNode ``slash #[mkAtom "\\"]⟩
abbrev Pipe : Grapheme := ⟨mkNode ``pipe #[mkAtom "|"]⟩
abbrev Semicolon : Grapheme := ⟨mkNode ``semicolon #[mkAtom ";"]⟩
abbrev Colon : Grapheme := ⟨mkNode ``colon #[mkAtom ":"]⟩
abbrev Apostrophe : Grapheme := ⟨mkNode ``apostrophe #[mkAtom "'"]⟩
abbrev Quote : Grapheme := ⟨mkNode ``quote #[mkAtom "\""]⟩
abbrev Comma : Grapheme := ⟨mkNode ``comma #[mkAtom ","]⟩
abbrev Period : Grapheme := ⟨mkNode ``period #[mkAtom "."]⟩
abbrev Langle : Grapheme := ⟨mkNode ``langle #[mkAtom "<"]⟩
abbrev Rangle : Grapheme := ⟨mkNode ``rangle #[mkAtom ">"]⟩
abbrev Divide : Grapheme := ⟨mkNode ``divide #[mkAtom "/"]⟩
abbrev Question : Grapheme := ⟨mkNode ``question #[mkAtom "?"]⟩
abbrev Grave : Grapheme := ⟨mkNode ``grave #[mkAtom "`"]⟩
abbrev Tilde : Grapheme := ⟨mkNode ``tilde #[mkAtom "~"]⟩

end Symbols

section Alphabet

abbrev alpha : Grapheme := ⟨mkNode ``«a» #[mkAtom "a"]⟩
abbrev beta : Grapheme := ⟨mkNode ``«b» #[mkAtom "b"]⟩
abbrev gamma : Grapheme := ⟨mkNode ``«c» #[mkAtom "c"]⟩
abbrev delta : Grapheme := ⟨mkNode ``«d» #[mkAtom "d"]⟩
abbrev epsilon : Grapheme := ⟨mkNode ``«e» #[mkAtom "e"]⟩
abbrev zeta : Grapheme := ⟨mkNode ``«f» #[mkAtom "f"]⟩
abbrev eta : Grapheme := ⟨mkNode ``«g» #[mkAtom "g"]⟩
abbrev theta : Grapheme := ⟨mkNode ``«h» #[mkAtom "h"]⟩
abbrev iota : Grapheme := ⟨mkNode ``«i» #[mkAtom "i"]⟩
abbrev kappa : Grapheme := ⟨mkNode ``«j» #[mkAtom "j"]⟩
abbrev lambda : Grapheme := ⟨mkNode ``«k» #[mkAtom "k"]⟩
abbrev mu : Grapheme := ⟨mkNode ``«l» #[mkAtom "l"]⟩
abbrev nu : Grapheme := ⟨mkNode ``«m» #[mkAtom "m"]⟩
abbrev xi : Grapheme := ⟨mkNode ``«n» #[mkAtom "n"]⟩
abbrev omicron : Grapheme := ⟨mkNode ``«o» #[mkAtom "o"]⟩
abbrev pi : Grapheme := ⟨mkNode ``«p» #[mkAtom "p"]⟩
abbrev rho : Grapheme := ⟨mkNode ``«q» #[mkAtom "q"]⟩
abbrev sigma : Grapheme := ⟨mkNode ``«r» #[mkAtom "r"]⟩
abbrev tau : Grapheme := ⟨mkNode ``«s» #[mkAtom "s"]⟩
abbrev upsilon : Grapheme := ⟨mkNode ``«t» #[mkAtom "t"]⟩
abbrev phi : Grapheme := ⟨mkNode ``«u» #[mkAtom "u"]⟩
abbrev chi : Grapheme := ⟨mkNode ``«v» #[mkAtom "v"]⟩
abbrev psi : Grapheme := ⟨mkNode ``«w» #[mkAtom "w"]⟩
abbrev omega : Grapheme := ⟨mkNode ``«x» #[mkAtom "x"]⟩
abbrev why : Grapheme := ⟨mkNode ``«y» #[mkAtom "y"]⟩
abbrev zed : Grapheme := ⟨mkNode ``«z» #[mkAtom "z"]⟩

abbrev Alpha : Grapheme := ⟨mkNode ``«A» #[mkAtom "A"]⟩
abbrev Beta : Grapheme := ⟨mkNode ``«B» #[mkAtom "B"]⟩
abbrev Gamma : Grapheme := ⟨mkNode ``«C» #[mkAtom "C"]⟩
abbrev Delta : Grapheme := ⟨mkNode ``«D» #[mkAtom "D"]⟩
abbrev Epsilon : Grapheme := ⟨mkNode ``«E» #[mkAtom "E"]⟩
abbrev Zeta : Grapheme := ⟨mkNode ``«F» #[mkAtom "F"]⟩
abbrev Eta : Grapheme := ⟨mkNode ``«G» #[mkAtom "G"]⟩
abbrev Theta : Grapheme := ⟨mkNode ``«H» #[mkAtom "H"]⟩
abbrev Iota : Grapheme := ⟨mkNode ``«I» #[mkAtom "I"]⟩
abbrev Kappa : Grapheme := ⟨mkNode ``«J» #[mkAtom "J"]⟩
abbrev Lambda : Grapheme := ⟨mkNode ``«K» #[mkAtom "K"]⟩
abbrev Mu : Grapheme := ⟨mkNode ``«L» #[mkAtom "L"]⟩
abbrev Nu : Grapheme := ⟨mkNode ``«M» #[mkAtom "M"]⟩
abbrev Xi : Grapheme := ⟨mkNode ``«N» #[mkAtom "N"]⟩
abbrev Omicron : Grapheme := ⟨mkNode ``«O» #[mkAtom "O"]⟩
abbrev Pi : Grapheme := ⟨mkNode ``«P» #[mkAtom "P"]⟩
abbrev Rho : Grapheme := ⟨mkNode ``«Q» #[mkAtom "Q"]⟩
abbrev Sigma : Grapheme := ⟨mkNode ``«R» #[mkAtom "R"]⟩
abbrev Tau : Grapheme := ⟨mkNode ``«S» #[mkAtom "S"]⟩
abbrev Upsilon : Grapheme := ⟨mkNode ``«T» #[mkAtom "T"]⟩
abbrev Phi : Grapheme := ⟨mkNode ``«U» #[mkAtom "U"]⟩
abbrev Chi : Grapheme := ⟨mkNode ``«V» #[mkAtom "V"]⟩
abbrev Psi : Grapheme := ⟨mkNode ``«W» #[mkAtom "W"]⟩
abbrev Omega : Grapheme := ⟨mkNode ``«X» #[mkAtom "X"]⟩
abbrev Why : Grapheme := ⟨mkNode ``«Y» #[mkAtom "Y"]⟩
abbrev Zed : Grapheme := ⟨mkNode ``«Z» #[mkAtom "Z"]⟩

end Alphabet

abbrev Leader (γ : Grapheme) : TermElabM Syntax.Tactic := `(tactic|leader% $γ)
abbrev Done : TermElabM Syntax.Tactic := `(tactic|done%)

def Key := Option (Grapheme ⊕ Terminal)

namespace Key

notation "spin%" => some (Sum.inr («α» := «Grapheme») default)
notation "turn% " γ => some (Sum.inl («α» := «Grapheme») («β» := «Terminal») γ)

@[simp] theorem spin_rfl : spin% = some (Sum.inr Carriage) := by rfl
@[simp] theorem turn_rfl : ∀ γ, (turn% γ) = some (Sum.inl γ) := by intro; rfl

@[coe]
def toPoint : Key → Point
| turn% γ => point% ⟨γ.raw⟩
| spin% => bot%
| _ => none

deriving instance TypeName for Key
instance : Inhabited Key := ⟨spin%⟩
instance : Encodable Key := by unfold Key; infer_instance
instance : Coe Key Point := ⟨toPoint⟩

def mk : Char → Key
| 'a' => turn% alpha
| 'b' => turn% beta
| 'c' => turn% gamma
| 'd' => turn% delta
| 'e' => turn% epsilon
| 'f' => turn% zeta
| 'g' => turn% eta
| 'h' => turn% theta
| 'i' => turn% iota
| 'j' => turn% kappa
| 'k' => turn% lambda
| 'l' => turn% mu
| 'm' => turn% nu
| 'n' => turn% xi
| 'o' => turn% omicron
| 'p' => turn% pi
| 'q' => turn% rho
| 'r' => turn% sigma
| 's' => turn% tau
| 't' => turn% upsilon
| 'u' => turn% phi
| 'v' => turn% chi
| 'w' => turn% psi
| 'x' => turn% omega
| 'y' => turn% why
| 'z' => turn% zed
| 'A' => turn% Alpha
| 'B' => turn% Beta
| 'C' => turn% Gamma
| 'D' => turn% Delta
| 'E' => turn% Epsilon
| 'F' => turn% Zeta
| 'G' => turn% Eta
| 'H' => turn% Theta
| 'I' => turn% Iota
| 'J' => turn% Kappa
| 'K' => turn% Lambda
| 'L' => turn% Mu
| 'M' => turn% Nu
| 'N' => turn% Xi
| 'O' => turn% Omicron
| 'P' => turn% Pi
| 'Q' => turn% Rho
| 'R' => turn% Sigma
| 'S' => turn% Tau
| 'T' => turn% Upsilon
| 'U' => turn% Phi
| 'V' => turn% Chi
| 'W' => turn% Psi
| 'X' => turn% Omega
| 'Y' => turn% Why
| 'Z' => turn% Zed
| '0' => turn% Zero
| '1' => turn% One
| '2' => turn% Two
| '3' => turn% Three
| '4' => turn% Four
| '5' => turn% Five
| '6' => turn% Six
| '7' => turn% Seven
| '8' => turn% Eight
| '9' => turn% Nine
| '!' => turn% Exclamation
| '@' => turn% Sign
| '#' => turn% Hash
| '$' => turn% Dollar
| '%' => turn% Percent
| '^' => turn% Caret
| '&' => turn% Ampersand
| '*' => turn% Asterisk
| '(' => turn% Lparen
| ')' => turn% Rparen
| '-' => turn% Hyphen
| '_' => turn% Underscore
| '=' => turn% Equals
| '+' => turn% Plus
| '[' => turn% Lbracket
| ']' => turn% Rbracket
| '{' => turn% Lbrace
| '}' => turn% Rbrace
| '|' => turn% Pipe
| ';' => turn% Semicolon
| ':' => turn% Colon
| '"' => turn% Quote
| ',' => turn% Comma
| '.' => turn% Period
| '<' => turn% Langle
| '>' => turn% Rangle
| '/' => turn% Divide
| '?' => turn% Question
| '`' => turn% Grave
| '~' => turn% Tilde
| ' ' => turn% Space
| '\\' => turn% Slash
| '\'' => turn% Apostrophe
| '\n' => spin%
| _ => none

def ofByteArray : ByteArray → Array Key
| ⟨γ⟩ => γ.map (Key.mk ∘ Char.ofUInt8)

def ofFin : Fin 97 → Key
| 0 => turn% Space
| 1 => turn% Exclamation
| 2 => turn% Quote
| 3 => turn% Hash
| 4 => turn% Dollar
| 5 => turn% Percent
| 6 => turn% Ampersand
| 7 => turn% Apostrophe
| 8 => turn% Lparen
| 9 => turn% Rparen
| 10 => turn% Asterisk
| 11 => turn% Plus
| 12 => turn% Comma
| 13 => turn% Hyphen
| 14 => turn% Period
| 15 => turn% Divide
| 16 => turn% Zero
| 17 => turn% One
| 18 => turn% Two
| 19 => turn% Three
| 20 => turn% Four
| 21 => turn% Five
| 22 => turn% Six
| 23 => turn% Seven
| 24 => turn% Eight
| 25 => turn% Nine
| 26 => turn% Colon
| 27 => turn% Semicolon
| 28 => turn% Langle
| 29 => turn% Equals
| 30 => turn% Rangle
| 31 => turn% Question
| 32 => turn% Sign
| 33 => turn% Alpha
| 34 => turn% Beta
| 35 => turn% Gamma
| 36 => turn% Delta
| 37 => turn% Epsilon
| 38 => turn% Zeta
| 39 => turn% Eta
| 40 => turn% Theta
| 41 => turn% Iota
| 42 => turn% Kappa
| 43 => turn% Lambda
| 44 => turn% Mu
| 45 => turn% Nu
| 46 => turn% Xi
| 47 => turn% Omicron
| 48 => turn% Pi
| 49 => turn% Rho
| 50 => turn% Sigma
| 51 => turn% Tau
| 52 => turn% Upsilon
| 53 => turn% Phi
| 54 => turn% Chi
| 55 => turn% Psi
| 56 => turn% Omega
| 57 => turn% Why
| 58 => turn% Zed
| 59 => turn% Lbracket
| 60 => turn% Slash
| 61 => turn% Rbracket
| 62 => turn% Caret
| 63 => turn% Underscore
| 64 => turn% Grave
| 65 => turn% alpha
| 66 => turn% beta
| 67 => turn% gamma
| 68 => turn% delta
| 69 => turn% epsilon
| 70 => turn% zeta
| 71 => turn% eta
| 72 => turn% theta
| 73 => turn% iota
| 74 => turn% kappa
| 75 => turn% lambda
| 76 => turn% mu
| 77 => turn% nu
| 78 => turn% xi
| 79 => turn% omicron
| 80 => turn% pi
| 81 => turn% rho
| 82 => turn% sigma
| 83 => turn% tau
| 84 => turn% upsilon
| 85 => turn% phi
| 86 => turn% chi
| 87 => turn% psi
| 88 => turn% omega
| 89 => turn% why
| 90 => turn% zed
| 91 => turn% Lbrace
| 92 => turn% Pipe
| 93 => turn% Rbrace
| 94 => turn% Tilde
| 95 => spin%
| _ => none

def toFin : Key → Fin 97
| turn% ⟨.node _ ``space _⟩ => 0
| turn% ⟨.node _ ``exclamation _⟩ => 1
| turn% ⟨.node _ ``quote _⟩ => 2
| turn% ⟨.node _ ``hash _⟩ => 3
| turn% ⟨.node _ ``dollar _⟩ => 4
| turn% ⟨.node _ ``percent _⟩ => 5
| turn% ⟨.node _ ``ampersand _⟩ => 6
| turn% ⟨.node _ ``apostrophe _⟩ => 7
| turn% ⟨.node _ ``lparen _⟩ => 8
| turn% ⟨.node _ ``rparen _⟩ => 9
| turn% ⟨.node _ ``asterisk _⟩ => 10
| turn% ⟨.node _ ``plus _⟩ => 11
| turn% ⟨.node _ ``comma _⟩ => 12
| turn% ⟨.node _ ``hyphen _⟩ => 13
| turn% ⟨.node _ ``period _⟩ => 14
| turn% ⟨.node _ ``divide _⟩ => 15
| turn% ⟨.node _ ``zero _⟩ => 16
| turn% ⟨.node _ ``one _⟩ => 17
| turn% ⟨.node _ ``two _⟩ => 18
| turn% ⟨.node _ ``three _⟩ => 19
| turn% ⟨.node _ ``four _⟩ => 20
| turn% ⟨.node _ ``five _⟩ => 21
| turn% ⟨.node _ ``six _⟩ => 22
| turn% ⟨.node _ ``seven _⟩ => 23
| turn% ⟨.node _ ``eight _⟩ => 24
| turn% ⟨.node _ ``nine _⟩ => 25
| turn% ⟨.node _ ``colon _⟩ => 26
| turn% ⟨.node _ ``semicolon _⟩ => 27
| turn% ⟨.node _ ``langle _⟩ => 28
| turn% ⟨.node _ ``equals _⟩ => 29
| turn% ⟨.node _ ``rangle _⟩ => 30
| turn% ⟨.node _ ``question _⟩ => 31
| turn% ⟨.node _ ``sign _⟩ => 32
| turn% ⟨.node _ ``«A» _⟩ => 33
| turn% ⟨.node _ ``«B» _⟩ => 34
| turn% ⟨.node _ ``«C» _⟩ => 35
| turn% ⟨.node _ ``«D» _⟩ => 36
| turn% ⟨.node _ ``«E» _⟩ => 37
| turn% ⟨.node _ ``«F» _⟩ => 38
| turn% ⟨.node _ ``«G» _⟩ => 39
| turn% ⟨.node _ ``«H» _⟩ => 40
| turn% ⟨.node _ ``«I» _⟩ => 41
| turn% ⟨.node _ ``«J» _⟩ => 42
| turn% ⟨.node _ ``«K» _⟩ => 43
| turn% ⟨.node _ ``«L» _⟩ => 44
| turn% ⟨.node _ ``«M» _⟩ => 45
| turn% ⟨.node _ ``«N» _⟩ => 46
| turn% ⟨.node _ ``«O» _⟩ => 47
| turn% ⟨.node _ ``«P» _⟩ => 48
| turn% ⟨.node _ ``«Q» _⟩ => 49
| turn% ⟨.node _ ``«R» _⟩ => 50
| turn% ⟨.node _ ``«S» _⟩ => 51
| turn% ⟨.node _ ``«T» _⟩ => 52
| turn% ⟨.node _ ``«U» _⟩ => 53
| turn% ⟨.node _ ``«V» _⟩ => 54
| turn% ⟨.node _ ``«W» _⟩ => 55
| turn% ⟨.node _ ``«X» _⟩ => 56
| turn% ⟨.node _ ``«Y» _⟩ => 57
| turn% ⟨.node _ ``«Z» _⟩ => 58
| turn% ⟨.node _ ``lbracket _⟩ => 59
| turn% ⟨.node _ ``slash _⟩ => 60
| turn% ⟨.node _ ``rbracket _⟩ => 61
| turn% ⟨.node _ ``caret _⟩ => 62
| turn% ⟨.node _ ``underscore _⟩ => 63
| turn% ⟨.node _ ``grave _⟩ => 64
| turn% ⟨.node _ ``«a» _⟩ => 65
| turn% ⟨.node _ ``«b» _⟩ => 66
| turn% ⟨.node _ ``«c» _⟩ => 67
| turn% ⟨.node _ ``«d» _⟩ => 68
| turn% ⟨.node _ ``«e» _⟩ => 69
| turn% ⟨.node _ ``«f» _⟩ => 70
| turn% ⟨.node _ ``«g» _⟩ => 71
| turn% ⟨.node _ ``«h» _⟩ => 72
| turn% ⟨.node _ ``«i» _⟩ => 73
| turn% ⟨.node _ ``«j» _⟩ => 74
| turn% ⟨.node _ ``«k» _⟩ => 75
| turn% ⟨.node _ ``«l» _⟩ => 76
| turn% ⟨.node _ ``«m» _⟩ => 77
| turn% ⟨.node _ ``«n» _⟩ => 78
| turn% ⟨.node _ ``«o» _⟩ => 79
| turn% ⟨.node _ ``«p» _⟩ => 80
| turn% ⟨.node _ ``«q» _⟩ => 81
| turn% ⟨.node _ ``«r» _⟩ => 82
| turn% ⟨.node _ ``«s» _⟩ => 83
| turn% ⟨.node _ ``«t» _⟩ => 84
| turn% ⟨.node _ ``«u» _⟩ => 85
| turn% ⟨.node _ ``«v» _⟩ => 86
| turn% ⟨.node _ ``«w» _⟩ => 87
| turn% ⟨.node _ ``«x» _⟩ => 88
| turn% ⟨.node _ ``«y» _⟩ => 89
| turn% ⟨.node _ ``«z» _⟩ => 90
| turn% ⟨.node _ ``lbrace _⟩ => 91
| turn% ⟨.node _ ``pipe _⟩ => 92
| turn% ⟨.node _ ``rbrace _⟩ => 93
| turn% ⟨.node _ ``tilde _⟩ => 94
| spin% => 95
| _ => 96

open Sodium Crypto Ethos in
def quantize {τ : Sodium σ} (scope : ScopeName := .global) : Key → CryptoM τ Observable
| turn% γ => do Observable.new <| ← `(tactic|leader% $γ)
| spin% => do Observable.new <| ← `(tactic|done%)
| _ => Observable.pointer scope

end Key

def Shape.pull : Shape → Key
| some (some γ) => Key.mk γ
| some none => spin%
| _ => none

def Shape.push : Key → Shape
| turn% ⟨.node _ ``space _⟩ => shape% ' '
| turn% ⟨.node _ ``exclamation _⟩ => shape% '!'
| turn% ⟨.node _ ``quote _⟩ => shape% '"'
| turn% ⟨.node _ ``hash _⟩ => shape% '#'
| turn% ⟨.node _ ``dollar _⟩ => shape% '$'
| turn% ⟨.node _ ``percent _⟩ => shape% '%'
| turn% ⟨.node _ ``ampersand _⟩ => shape% '&'
| turn% ⟨.node _ ``apostrophe _⟩ => shape% '\''
| turn% ⟨.node _ ``lparen _⟩ => shape% '('
| turn% ⟨.node _ ``rparen _⟩ => shape% ')'
| turn% ⟨.node _ ``asterisk _⟩ => shape% '*'
| turn% ⟨.node _ ``plus _⟩ => shape% '+'
| turn% ⟨.node _ ``comma _⟩ => shape% ','
| turn% ⟨.node _ ``hyphen _⟩ => shape% '-'
| turn% ⟨.node _ ``period _⟩ => shape% '.'
| turn% ⟨.node _ ``divide _⟩ => shape% '/'
| turn% ⟨.node _ ``zero _⟩ => shape% '0'
| turn% ⟨.node _ ``one _⟩ => shape% '1'
| turn% ⟨.node _ ``two _⟩ => shape% '2'
| turn% ⟨.node _ ``three _⟩ => shape% '3'
| turn% ⟨.node _ ``four _⟩ => shape% '4'
| turn% ⟨.node _ ``five _⟩ => shape% '5'
| turn% ⟨.node _ ``six _⟩ => shape% '6'
| turn% ⟨.node _ ``seven _⟩ => shape% '7'
| turn% ⟨.node _ ``eight _⟩ => shape% '8'
| turn% ⟨.node _ ``nine _⟩ => shape% '9'
| turn% ⟨.node _ ``colon _⟩ => shape% ':'
| turn% ⟨.node _ ``semicolon _⟩ => shape% ';'
| turn% ⟨.node _ ``langle _⟩ => shape% '<'
| turn% ⟨.node _ ``equals _⟩ => shape% '='
| turn% ⟨.node _ ``rangle _⟩ => shape% '>'
| turn% ⟨.node _ ``question _⟩ => shape% '?'
| turn% ⟨.node _ ``sign _⟩ => shape% '@'
| turn% ⟨.node _ ``«A» _⟩ => shape% 'A'
| turn% ⟨.node _ ``«B» _⟩ => shape% 'B'
| turn% ⟨.node _ ``«C» _⟩ => shape% 'C'
| turn% ⟨.node _ ``«D» _⟩ => shape% 'D'
| turn% ⟨.node _ ``«E» _⟩ => shape% 'E'
| turn% ⟨.node _ ``«F» _⟩ => shape% 'F'
| turn% ⟨.node _ ``«G» _⟩ => shape% 'G'
| turn% ⟨.node _ ``«H» _⟩ => shape% 'H'
| turn% ⟨.node _ ``«I» _⟩ => shape% 'I'
| turn% ⟨.node _ ``«J» _⟩ => shape% 'J'
| turn% ⟨.node _ ``«K» _⟩ => shape% 'K'
| turn% ⟨.node _ ``«L» _⟩ => shape% 'L'
| turn% ⟨.node _ ``«M» _⟩ => shape% 'M'
| turn% ⟨.node _ ``«N» _⟩ => shape% 'N'
| turn% ⟨.node _ ``«O» _⟩ => shape% 'O'
| turn% ⟨.node _ ``«P» _⟩ => shape% 'P'
| turn% ⟨.node _ ``«Q» _⟩ => shape% 'Q'
| turn% ⟨.node _ ``«R» _⟩ => shape% 'R'
| turn% ⟨.node _ ``«S» _⟩ => shape% 'S'
| turn% ⟨.node _ ``«T» _⟩ => shape% 'T'
| turn% ⟨.node _ ``«U» _⟩ => shape% 'U'
| turn% ⟨.node _ ``«V» _⟩ => shape% 'V'
| turn% ⟨.node _ ``«W» _⟩ => shape% 'W'
| turn% ⟨.node _ ``«X» _⟩ => shape% 'X'
| turn% ⟨.node _ ``«Y» _⟩ => shape% 'Y'
| turn% ⟨.node _ ``«Z» _⟩ => shape% 'Z'
| turn% ⟨.node _ ``lbracket _⟩ => shape% '['
| turn% ⟨.node _ ``slash _⟩ => shape% '\\'
| turn% ⟨.node _ ``rbracket _⟩ => shape% ']'
| turn% ⟨.node _ ``caret _⟩ => shape% '^'
| turn% ⟨.node _ ``underscore _⟩ => shape% '_'
| turn% ⟨.node _ ``grave _⟩ => shape% '`'
| turn% ⟨.node _ ``«a» _⟩ => shape% 'a'
| turn% ⟨.node _ ``«b» _⟩ => shape% 'b'
| turn% ⟨.node _ ``«c» _⟩ => shape% 'c'
| turn% ⟨.node _ ``«d» _⟩ => shape% 'd'
| turn% ⟨.node _ ``«e» _⟩ => shape% 'e'
| turn% ⟨.node _ ``«f» _⟩ => shape% 'f'
| turn% ⟨.node _ ``«g» _⟩ => shape% 'g'
| turn% ⟨.node _ ``«h» _⟩ => shape% 'h'
| turn% ⟨.node _ ``«i» _⟩ => shape% 'i'
| turn% ⟨.node _ ``«j» _⟩ => shape% 'j'
| turn% ⟨.node _ ``«k» _⟩ => shape% 'k'
| turn% ⟨.node _ ``«l» _⟩ => shape% 'l'
| turn% ⟨.node _ ``«m» _⟩ => shape% 'm'
| turn% ⟨.node _ ``«n» _⟩ => shape% 'n'
| turn% ⟨.node _ ``«o» _⟩ => shape% 'o'
| turn% ⟨.node _ ``«p» _⟩ => shape% 'p'
| turn% ⟨.node _ ``«q» _⟩ => shape% 'q'
| turn% ⟨.node _ ``«r» _⟩ => shape% 'r'
| turn% ⟨.node _ ``«s» _⟩ => shape% 's'
| turn% ⟨.node _ ``«t» _⟩ => shape% 't'
| turn% ⟨.node _ ``«u» _⟩ => shape% 'u'
| turn% ⟨.node _ ``«v» _⟩ => shape% 'v'
| turn% ⟨.node _ ``«w» _⟩ => shape% 'w'
| turn% ⟨.node _ ``«x» _⟩ => shape% 'x'
| turn% ⟨.node _ ``«y» _⟩ => shape% 'y'
| turn% ⟨.node _ ``«z» _⟩ => shape% 'z'
| turn% ⟨.node _ ``lbrace _⟩ => shape% '{'
| turn% ⟨.node _ ``pipe _⟩ => shape% '|'
| turn% ⟨.node _ ``rbrace _⟩ => shape% '}'
| turn% ⟨.node _ ``tilde _⟩ => shape% '~'
| spin% => some none
| _ => none

open Sodium Crypto Ethos

structure _root_.IO.RealWorld.Key (τ : Sodium σ) where
  key : Typography.Key
  witness : Witness τ := ⟨default, fun _ => key.quantize⟩

/--
Mechanism for elaborating keypresses.
-/
def Typewriter (τ : Sodium σ) : PFunctor where
  «A» := IO.RealWorld.Key τ
  «B» | ⟨none, _⟩ => PEmpty
      | ⟨spin%, _⟩ => Tactic
      | ⟨turn% _, _⟩ => TermElabM Shape

namespace Typewriter

variable {τ : Sodium σ}

instance : Coe (IO.RealWorld.Key τ) (Typewriter τ).A := ⟨id⟩
instance : Coe (Typewriter τ).A (IO.RealWorld.Key τ) := ⟨id⟩

@[simp] theorem typewriter_key_idx : (Typewriter τ).A = IO.RealWorld.Key τ := by rfl
@[simp] theorem typewriter_norm_idx : ∀ α, (Typewriter τ).B ⟨none, α⟩ = PEmpty := by intro; rfl
@[simp] theorem typewriter_spin_idx : ∀ α (γ : Terminal), (Typewriter τ).B ⟨some (.inr γ), α⟩ = Tactic := by intros; rfl
@[simp] theorem typewriter_turn_idx : ∀ α (γ : Grapheme), (Typewriter τ).B ⟨turn% γ, α⟩ = TermElabM Shape := by intros; rfl

instance : Inhabited (Typewriter τ).A := ⟨⟨default, default⟩⟩
instance {α} : Inhabited (Typewriter τ α) := ⟨⟨none, default⟩, PEmpty.elim⟩

protected def map {α β} := @PFunctor.map α β (Typewriter τ)

def enter (γ : String) (on : String := ";") (action : IO Unit := IO.eprint "\n") : Tactic
| `(tactic|leader% $δ) => do
  unless γ.endsWith ⟨[← parse δ]⟩ do throwAbortTactic
  action
| `(tactic|done%) => do
  let γ := γ.dropRightWhile (· = ' ')
  unless γ.endsWith on do throwAbortTactic
  action
| _ => throwUnsupportedSyntax

/--
Given a `TermElabM Shape`, attempt to resolve ⊢ `ULift Char`.
-/
@[aesop unsafe 97% destruct (rule_sets := [«standard»])]
def norm (γ : TermElabM Shape) : TacticM PUnit := do
  match Shape.pull (← runTermElab γ) with
  | turn% γ => evalTactic <| ← `(tactic|leader% $γ)
  | spin% => evalTactic <| ← `(tactic|done%)
  | _ => throwUnsupportedSyntax

def write (γ : IO.RealWorld.Key τ) (δ : Tactic := enter default) : TacticM ((Typewriter τ).B γ) :=
  match γ with
  | ⟨turn% γ, _⟩ => return (Shape.push ∘ Key.mk) <$> parse γ
  | ⟨spin%, _⟩ => pure δ
  | _ => throwUnsupportedSyntax

def read {γ : IO.RealWorld.Key τ} (writer : TacticM ((Typewriter τ).B γ)) : TacticM Unit := do
  match γ with
  | ⟨turn% _, _⟩ => norm (← writer)
  | ⟨spin%, _⟩ => (← writer) <| ← `(tactic|done%)
  | _ => throwUnsupportedSyntax

/--
Source `IO.RealWorld.Key τ` from stdin without buffering.
-/
def getKeyFromCore : CoreM (Option (IO.RealWorld.Key τ)) := do
  let fd ← IO.getStdin
  let mut key? : Option (IO.RealWorld.Key τ) := none
  repeat match ← fd.read 1 with
  | ⟨#[]⟩ => continue
  | ⟨#[γ]⟩ => key? := some { key := Key.mk <| Char.ofUInt8 γ }; break
  | _ => break
  return key?

/--
Given a `Typewriter τ Tactic`, attempt to resolve ⊢ `ULift String`.

Progress is echoed on stderr. Witnesses are printed to stdout.

By default, keys are sourced from stdin (see `getKeyFromCore`).
-/
protected def observe
  (writer : Typewriter τ Tactic)
  (δ : String → Tactic := enter)
  (ε : CoreM (Option (IO.RealWorld.Key τ)) := getKeyFromCore)
  (pre : String := default)
  (post : String := default)
  : TacticM (Witness τ) :=
do match writer with
| ⟨⟨spin%, α⟩, press⟩ =>
  let mut buf : String := pre
  try
    repeat match ← ε with
    | some key =>
      let γ ← mkFreshExprMVar (userName := `«γ») <| mkApp (mkConst ``ULift [levelZero]) (mkConst ``Char)
      let _ ← Tactic.run γ.mvarId! <| read <| write key (δ buf)
      let γ ← instantiateMVars γ
      let γ ← Tactic.elabTermEnsuringType (← delab <| mkApp (mkConst ``ULift.down) γ) (mkConst ``Char)
      let γ := String.mk [← unsafe evalExpr Char (mkConst ``Char) γ]
      IO.eprint γ
      buf := buf ++ γ
    | _ => throwAbortTactic
    return default
  catch ex => do
    unless isAbortTacticException ex do throw ex
    let γ ← delab <| mkStrLit (buf ++ post)
    let γ ← `(tactic|exact ⟨$γ⟩)
    press evalTactic γ
    return by refine Universal.map (bind · fun α => ?_) α; exact do
      -- Provide a witness for `ULift String` using the computed value.
      unless α.phase = .safe do return α
      let γ ← Observable.new γ .global
      γ.emit (← IO.getStdout) "$/spin"
      return γ
| ⟨⟨turn% γ, α⟩, press⟩ =>
  press (Shape.push <$> do IO.eprint (← parse γ); pure (turn% γ)) <| ← `(tactic|done%)
  return by refine Universal.map (bind · fun α => ?_) α; exact do
    -- Provide a witness for `ULift String` by encoding the given grapheme as a Json string.
    let γ ← Observable.new <| ← `(tactic|leader% $γ)
    let γ ← γ.quantize (if α.phase = .norm then .down else if α.phase = .safe then .left else .right)
    γ.emit (← IO.getStdout) "$/turn"
    return γ
| ⟨⟨none, α⟩, _⟩ => pure α

protected def auto
  (ictx : InputContext)
  (writer : Typewriter τ Tactic)
  (δ : String → Tactic := enter)
  (pre : String := default)
  (post : String := default)
  : TacticM (Witness τ) :=
do
  let ref ← IO.mkRef ictx.input.data
  Typewriter.observe writer δ (pre := pre) (post := post) do
    match ← ref.get with
    | [] => pure none
    | ε :: δ => ref.set δ; return some { key := Key.mk ε }

protected def print
  (writer : Typewriter τ Tactic)
  (δ : String → Tactic := enter)
  (ε : CoreM (Option (IO.RealWorld.Key τ)) := getKeyFromCore)
  (pre : String := default)
  (post : String := default)
  : TacticM String :=
do
  let γ ← mkFreshExprMVar (userName := `«γ») <| mkApp (mkConst ``ULift [levelZero]) (mkConst ``String)
  let _ ← Tactic.run γ.mvarId! <| discard <| Typewriter.observe writer δ ε pre post
  let γ ← instantiateMVars γ
  let γ ← Tactic.elabTermEnsuringType (← delab <| mkApp (mkConst ``ULift.down) γ) (mkConst ``String)
  unsafe evalExpr String (mkConst ``String) γ

@[aesop unsafe 97% forward (rule_sets := [«cautious»])]
protected def forward (ictx : InputContext) (writer : Typewriter τ Tactic) : Tactic :=
  fun _ => discard <| Typewriter.auto ictx writer

def _root_.IO.RealWorld.Typist (τ : Sodium σ) := Emulator σ ⊚ Typewriter τ
def _root_.IO.RealWorld.Automaton (τ : Sodium σ) := Typewriter τ ⊚ Emulator σ

end Typewriter

export IO.RealWorld (Typist Automaton)

end Typography

export Typography (
  Typewriter
  Typewriter.map
  Typewriter.observe
  Typewriter.auto
  Typewriter.print
  Typewriter.forward
  Typist
  Automaton
)
