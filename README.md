# DREAM: Data-dRiven pREdictive fArMing #
### @Politecnico di Milano, Academic Year 2021-2022, Software Engineering II course ###
This repository contains the Requirement Analysis Document, the Design Document and an Alloy representation of the DREAM application, used to make it easy communication and help among Indian farmers and Indian government. This project is related specifically to the Telengana Indian region.
<p align="center">
<img src=https://github.com/marcozetaa/DeSantisTerzianiZanghieri/blob/main/comp/Mockup/PNG/DREAM%20LOGO/DREAM%20LOGO-1.png width="60%" align="center">
</p>

## Characters ##
- **Farmer**: Anyone involved in the field of agriculture. It interacts with the system by updating the data and asking for help;
- **Agronomist**: Anyone responsible for a single land in the region. With the system, he manage the farmers in his land and eventually helps them;
- **Policy Maker**: Anyone that has the overall view of the Telengana region and use the system to evaluate and intervene in case of bad performance of both farmers and agronomists.
- 
## Goals ##
- Design a system able to make Farmers in communication among them and with the Agronomist in charge of the specific land;
- Allow Farmers to ask for help and being helped by other Farmers and by the Agronomist;
- Alert Farmers in case of bad meteorological weather;
- Allow the Agronomist to book a visit to the Farmer's land adn to visualize Farmers’ performance evaluation;
- Help Farmers improve their production.


## Proposed Solution ##
In the proposed solution, each Farmer will be equipped with an industrial serialized tabled to be kept in the farm. Each farmer will have its own authentication method and can use the table to insert useful data about the crop, access the Farmers' Forum, send messages to the Agronomist and visualize possible weather alerts.  
The Agronomist instead access the platform through its own device. They can plan a visit through a shared calendad with the Farmer, visualize data about the crops and message Farmers if necessary.  
The Policy Maker is designed by the government and can use the platform through its own device. He can visualize data about the crops and the wheather and sends periodical reports to the Agronomist regarding the performance of production.

### Component View ###
Here we can see the interaction among all the Services and Managers.
<p align="center">
<img src=https://github.com/marcozetaa/DeSantisTerzianiZanghieri/blob/main/comp/ComponentDiagrams/ComponentDiagram.png width="60%" align="center">
</p>

### Component Inteface ###
In the Component Interface we define all the methods and functions necessary for each one of the components.
<p align="center">
<img src=https://github.com/marcozetaa/DeSantisTerzianiZanghieri/blob/main/comp/ComponentDiagrams/Component%20Interface.png width="95%" align="center">
</p>

### Mockups ###
<p align="center">
<img src=https://github.com/marcozetaa/DeSantisTerzianiZanghieri/blob/main/comp/Mockup/PNG/FARMER/FARMER-2.png width="60%" align="center">
<img src=https://github.com/marcozetaa/DeSantisTerzianiZanghieri/blob/main/comp/Mockup/PNG/AGRONOMIST/AGRONOMIST-1.png width="60%" align="center">
<img src=https://github.com/marcozetaa/DeSantisTerzianiZanghieri/blob/main/comp/Mockup/PNG/POLICY%20MAKER/POLICY%20MAKER-1.png width="60%" align="center">
</p>






### Authors: Marco Zanghieri, Michele Terziani, Gabriele De Santis
