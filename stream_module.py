class mblk_t:
    """Simple message block holding byte data."""

    def __init__(self, data: bytes):
        self.data = bytearray(data)


class queue_t:
    """FIFO queue of message blocks."""

    def __init__(self):
        self._msgs = []

    def put(self, mblk: mblk_t) -> None:
        self._msgs.append(mblk)

    def get(self) -> mblk_t | None:
        if not self._msgs:
            return None
        return self._msgs.pop(0)


def attach_module(modules):
    """Chain module callables into a processing pipeline."""

    def _run(mblk: mblk_t) -> mblk_t:
        for mod in modules:
            mblk = mod(mblk)
        return mblk

    return _run
