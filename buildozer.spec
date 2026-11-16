[app]

title = محلل الذهب الاحترافي V2.3
package.name = goldproanalyzer
package.domain = org.goldpro
source.dir = .
source.include_exts = py,png,jpg,kv,atlas,ttf,csv
version = 2.3
requirements = python3,kivy,requests,arabic-reshaper,python-bidi
orientation = portrait
fullscreen = 0

# Internet access is required to retrieve XAU/USD market data.
android.permissions = INTERNET
android.api = 35
android.minapi = 23
android.ndk = 27b
android.archs = arm64-v8a,armeabi-v7a
android.accept_sdk_license = True

[buildozer]
log_level = 2
warn_on_root = 1
