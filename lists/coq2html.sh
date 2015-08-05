#!/bin/bash
coqdoc $1 -utf8 -html -s -interpolate --with-header ../header.html --no-glob --parse-comments
