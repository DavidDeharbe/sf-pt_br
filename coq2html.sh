#!/bin/sh
coqdoc --html --with-header header.html --utf8 $1 --parse-comments --interpolate --no-index --no-glob
