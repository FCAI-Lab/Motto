From Perennial.program_proof.session Require Export gossip.

Section CLIENT.

Import ClientSide SessionClient.

Context `{hG: !heapGS Σ}.

End CLIENT.

Section SERVER.

Import ServerSide SessionServer.

Context `{hG: !heapGS Σ}.

End SERVER.
