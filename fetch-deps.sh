#!/bin/bash

echo "Creating Dir"
mkdir -p dependencies/
cd dependencies/

echo "Fetching Deps"

echo "Fetching xml"
git clone https://github.com/jfdm/idris-xml.git xml
cd xml/
idris --install xml.ipkg
idris --installdoc xml.ipkg
cd ../


echo "Fetching containers"
git clone https://github.com/jfdm/idris-containers.git containers
cd containers/
idris --install containers.ipkg
idris --installdoc containers.ipkg
cd ../


echo "Fetching commons"
git clone https://github.com/jfdm/idris-commons.git commons
cd commons/
idris --install commons.ipkg
idris --installdoc commons.ipkg
cd ../

echo "Fetching Edda"
git clone https://github.com/jfdm/edda.git edda
cd edda/
idris --install edda.ipkg
idris --installdoc edda.ipkg
cd ../


cd ../
