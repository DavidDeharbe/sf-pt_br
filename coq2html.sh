#!/bin/sh
coqdoc --html --with-header header.html --utf8 $1 --interpolate --no-index --no-glob --no-lib-name
