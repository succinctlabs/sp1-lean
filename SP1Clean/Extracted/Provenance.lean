/-! # AUTO-GENERATED extraction provenance — do not edit by hand.

The semantic revision is unmodified upstream SP1. The extractor revision is an audited
descendant whose machine-source diff is reflection metadata only; exporter implementation
changes live outside the AIR definitions. Regenerate with `update_extracted.py`. -/

namespace SP1Clean.Extracted

/-- Exact two-revision boundary behind every checked-in extracted artifact. -/
structure ExtractionProvenance where
  semanticRevision : String
  extractorRevision : String
  extractorPatchSha256 : String
deriving DecidableEq, Repr

/-- Provenance validated by the generator before it writes any AIR artifact. -/
def checkedInProvenance : ExtractionProvenance where
  semanticRevision := "a630089d9ff484ec6f2feade8d0afbb1447eed11"
  extractorRevision := "69a8377c6e5550451f40c81fca17459687cd0a8f"
  extractorPatchSha256 := "a2c43cfab00280f5331a15ec251a8341a26ecf3baedcda22fec182915fbcf108"

end SP1Clean.Extracted
