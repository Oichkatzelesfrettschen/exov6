import Foundation

@_cdecl("LLVMFuzzerTestOneInput")
public func fuzz(_ ptr: UnsafePointer<UInt8>?, _ size: Int) -> Int32 {
    guard let ptr = ptr else { return 0 }
    let data = Data(bytes: ptr, count: size)
    if data == Data("crash".utf8) {
        fatalError("crash triggered")
    }
    return 0
}
