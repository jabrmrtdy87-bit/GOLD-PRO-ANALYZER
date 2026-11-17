[app]

# (str) Title of your application
title = Gold Pro V17

# (str) Package name
package.name = goldpro

# (str) Package domain (needed for android/ios packaging)
package.domain = org.test

# (str) Source code where the main.py live
source.dir = .

# (list) Source files to include (let empty to include all the files)
source.include_exts = py,png,jpg,kv,atlas,json,csv

# (str) Application versioning (method 1)
version = 17.0

# (list) Application requirements
# تم إضافة cython هنا لضمان توافقه مع البناء
requirements = python3,kivy,requests,cython

# (str) Orientation
orientation = portrait

# (list) Permissions
android.permissions = INTERNET,ACCESS_NETWORK_STATE

# (int) Target Android API
android.api = 33

# (int) Minimum API your APK will support.
android.minapi = 21

# (str) Android NDK version to use
android.ndk = 25b

# (list) The Android archs to build for
android.archs = arm64-v8a, armeabi-v7a

# (str) python-for-android branch to use, defaults to master
p4a.branch = master


# ===============================================================
# ✅ التصحيحات الأساسية التي تمت إضافتها (كانت مفقودة في ملفك):
# ===============================================================

# إجبار Buildozer على قبول تراخيص Android SDK تلقائياً
android.accept_sdk_license = True

# منع تحديث الـ SDK لتجنب المشاكل في بيئة GitHub Actions
android.skip_update = False

# إظهار تفاصيل أكثر في السجل (مفيد جداً في حال حدوث خطأ)
log_level = 2

# مسار الملف الرئيسي (تأكد أن اسم ملف البايثون الخاص بك هو main.py)
# إذا كان اسمه مختلفاً، قم بإزالة علامة المربع (#) واكتب الاسم الصحيح
# main.py = your_script_name.py
