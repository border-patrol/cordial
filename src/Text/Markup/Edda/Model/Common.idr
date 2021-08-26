module Text.Markup.Edda.Model.Common

%default total
%access public export

data FontTy   = SerifTy | SansTy | ScapTy | MonoTy
data QuoteTy  = SQuote | DQuote
data CiteSty  = ParenSty | TextSty
data ParenTy  = Parents | Brackets | Braces
data LinkTy   = HyperTy | ExposedTy | FnoteTy | RefTy | CiteTy
data MarkupTy = BoldTy | EmphTy | StrikeTy | UlineTy
data RawTy    = VerbTy | CodeTy | MathTy

data TextBlockTy = ParaTy | TheoremTy | CorollaryTy | LemmaTy | PropositionTy | ProofTy | DefinitionTy
               | ExerciseTy | NoteTy | ProblemTy | QuestionTy | RemarkTy
               | SolutionTy | ExampleTy | QuotationTy

data VerbBlockTy = CommentTy | ListingTy | LiteralTy | EquationTy

data ListTy = BulletTy | NumberTy

||| Add different block types but that will require adding predicated lists
data EddaTy = INLINE | BLOCK | SNIPPET | DOC

data ValidSnippet : EddaTy -> Type where
  IsInLine : ValidSnippet INLINE
  IsBlock  : ValidSnippet BLOCK

implementation Eq EddaTy where
    (==) INLINE  INLINE  = True
    (==) BLOCK   BLOCK   = True
    (==) DOC     DOC     = True
    (==) SNIPPET SNIPPET = True
    (==) _      _        = False

implementation Eq FontTy where
    (==) SerifTy SerifTy = True
    (==) SansTy  SansTy  = True
    (==) ScapTy  ScapTy  = True
    (==) MonoTy  MonoTy  = True
    (==) _       _       = False

implementation Eq QuoteTy where
    (==) SQuote SQuote = True
    (==) DQuote DQuote = True
    (==) _      _      = False

implementation Eq CiteSty where
    (==) ParenSty ParenSty = True
    (==) TextSty  TextSty  = True
    (==) _        _        = False

implementation Eq ParenTy where
    (==) Parents  Parents  = True
    (==) Brackets Brackets = True
    (==) Braces   Braces   = True
    (==) _        _        = False

implementation Eq LinkTy where
    (==) HyperTy   HyperTy   = True
    (==) ExposedTy ExposedTy = True
    (==) FnoteTy   FnoteTy   = True
    (==) RefTy     RefTy     = True
    (==) CiteTy    CiteTy    = True
    (==) _         _         = False

implementation Eq MarkupTy where
    (==) BoldTy   BoldTy   = True
    (==) EmphTy   EmphTy   = True
    (==) StrikeTy StrikeTy = True
    (==) UlineTy  UlineTy  = True
    (==) _        _        = False

implementation Eq RawTy where
    (==) VerbTy VerbTy = True
    (==) CodeTy CodeTy = True
    (==) MathTy MathTy = True
    (==) _      _      = False

implementation Eq VerbBlockTy where
    (==) CommentTy  CommentTy  = True
    (==) ListingTy  ListingTy  = True
    (==) LiteralTy  LiteralTy  = True
    (==) EquationTy EquationTy = True
    (==) _          _          = False

implementation Eq TextBlockTy where
    (==) ParaTy         ParaTy        = True
    (==) TheoremTy      TheoremTy     = True
    (==) CorollaryTy    CorollaryTy   = True
    (==) LemmaTy        LemmaTy       = True
    (==) PropositionTy  PropositionTy = True
    (==) ProofTy        ProofTy       = True
    (==) DefinitionTy   DefinitionTy  = True

    (==) ExerciseTy     ExerciseTy    = True
    (==) NoteTy         NoteTy        = True
    (==) ProblemTy      ProblemTy     = True
    (==) QuestionTy     QuestionTy    = True
    (==) RemarkTy       RemarkTy      = True

    (==) SolutionTy     SolutionTy    = True
    (==) ExampleTy      ExampleTy     = True
    (==) QuotationTy    QuotationTy   = True
    (==) _              _             = False

implementation Eq ListTy where
  (==) BulletTy BulletTy = True
  (==) NumberTy NumberTy = True
  (==) _        _        = False
