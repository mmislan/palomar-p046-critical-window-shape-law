# Reproducing the manuscript

Run `python check_paper.py` with Python 3 and matplotlib installed. The script checks finite enumerations and numerical bounds, writes `check_paper_output.json`, and regenerates the figure and CSV. Integer and rational comparisons are exact; rounded displays, the trial-count scale estimate and plots use floating point. These checks do not prove the universal mathematical statements.

Build the manuscript with `pdflatex main`, `bibtex main`, then `pdflatex main` twice. Formal verification evidence and exact source hashes are in `../../../verification/`.
