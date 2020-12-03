#!/bin/sh
set -e

LC_COLLATE=C # Enforce known sort order

committers=$(git shortlog -se HEAD | cut -f2,3 | sort)

# Sort contributors (different systems have slightly different soting logics)
cat CONTRIBUTORS | sort > SCONTRIBUTORS
missing_authors=$(echo "$committers" | comm -13 SCONTRIBUTORS -)
missing_authors=$(echo ${missing_authors} | sed 's/Caleb Donovick <donovick@cs.stanford.edu>//' )
missing_authors=$(echo ${missing_authors} | sed 's/Guillem Francès <guillem.frances@upf.edu>//' )
missing_authors=$(echo ${missing_authors} | sed 's/Matthew Fernandez <matthew.fernandez@gmail.com>//' )

if [ -n "$missing_authors" ]
then
  echo "$missing_authors" | awk '{print "::error file=SCONTRIBUTORS,line=0::💥 MISSING: " $0}'

  echo "💥 Some committers do NOT appear in CONTRIBUTORS 💥"
  echo ""
  echo "$missing_authors"
  echo "== Note: The following contributors are not committers. Do we need to update .mailmap? =="
  echo "$committers" | comm -23 SCONTRIBUTORS -
  exit 1
else
  echo "== Note: The following contributors were checked"
  echo "$committers" | comm -12 SCONTRIBUTORS -
  echo "All good!"
fi
