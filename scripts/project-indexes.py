"""Run the shared index generator using only the Python standard library."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "python"))

from lean_pool.indexes import main  # noqa: E402

sys.exit(main())
