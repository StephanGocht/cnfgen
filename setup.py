from setuptools import setup

setup(name='CnfGen',
      version='0.5',
      description='CNF formula generator',
      author='Massimo Lauria',
      author_email='lauria@kth.se',
      url='https://github.com/MassimoLauria/cnfgen',
      packages =['cnfformula'],
      entry_points = {
          'console_scripts': ['cnfgen=cnfformula.cnfgen:command_line_utility'],
      }
     )
