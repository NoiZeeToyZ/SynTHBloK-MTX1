// SynTHBloK-MTX1: registers this plugin's modules.
#include "plugin.hpp"

Plugin* pluginInstance;

extern Model* modelSynTHBloKJam;

void init(Plugin* p) {
    pluginInstance = p;
    p->addModel(modelSynTHBloKJam);
}
