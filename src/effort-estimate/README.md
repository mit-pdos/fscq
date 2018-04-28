# Measuring FSCQ security diff

- Install dependencies with `pip3 install -r requirements.txt`
- Get the base where `security` branch work started with `git merge-base origin/security origin/master` (it's `826eb7f6f9a1882f4c69a27f5e5d63ec7b0eb7fc`)
- Get an initial diff `git diff 826eb7f6f9a188..origin/security > security.diff`
- Split that with `./file-diffs.py security.diff -o diffs`
- Update the `diffs` directory by re-running; reports diffs that actually
  changed so they can be re-processed
- run `counts.py diffs/b/src/*.diff*` to add up deleted/added lines (see the file for the categorization)
