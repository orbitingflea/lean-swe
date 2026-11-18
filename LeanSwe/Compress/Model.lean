namespace LeanSwe.Compress

/-- Explicit environment removals clearing inherited codec configuration variables while keeping `PATH`. -/
def codecSanitizedEnv : Array (String × Option String) :=
  #[("XZ_OPT", none),
    ("XZ_DEFAULTS", none),
    ("ZSTD_CLEVEL", none),
    ("ZSTD_NBTHREADS", none),
    ("GZIP", none)]

end LeanSwe.Compress
