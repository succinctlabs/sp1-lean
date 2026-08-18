/-! # AUTO-GENERATED extraction provenance — do not edit by hand.

The semantic revision is unmodified upstream SP1. The extractor revision is an audited
descendant whose machine-source diff is reflection metadata only; exporter implementation
changes live outside the AIR definitions. Regenerate with `update_extracted.py`. -/

namespace SP1Clean.Extracted

/-- Exact two-revision boundary behind every checked-in extracted artifact. -/
structure ExtractionProvenance where
  semanticRevision : String
  extractorRevision : String
deriving DecidableEq, Repr

/-- Provenance validated by the generator before it writes any AIR artifact. -/
def checkedInProvenance : ExtractionProvenance where
  semanticRevision := "f66b4bff51d0ccff51d152e0f7f66b2ffedf3529"
  extractorRevision := "2b7ce14421535303659c1799f4af284eb8d72cee"

end SP1Clean.Extracted
