import os
from cobra.io import read_sbml_model
import blind_iml1515_joint_metabolic_v1 as protocol

# Compatibility correction after run 1 stopped before model load and before any
# metabolic outcome was computed. COBRApy 0.30.0 requested the BiGG model over
# an http URL and rejected the repository's 301 redirect to https. The workflow
# now downloads the exact same iML1515 SBML resource explicitly over HTTPS and
# this wrapper substitutes only the transport/loading mechanism.
MODEL_PATH = os.environ.get("INSACERMO_IML1515_SBML", "/tmp/iML1515.xml")


def load_model_https_compat(_model_id):
    return read_sbml_model(MODEL_PATH)


protocol.load_model = load_model_https_compat
print("COMPATIBILITY_CORRECTION model transport only; run 1 produced no metabolic outcomes")
protocol.main()
